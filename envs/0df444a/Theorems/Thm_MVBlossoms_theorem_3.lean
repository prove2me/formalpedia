-- Prove2me | Theorems.Thm_MVBlossoms_theorem_3
-- name    : MVBlossoms.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:47:19.316565+00:00
-- url     : https://prove2.me/theorems/98821989-8de0-4910-b9a4-41555d8412b4
-- title:
--   Theorem 3 — at every eligible tenacity: max level paths contain a bridge, bases are unique, shortest paths split at the base, blossoms are laminar, BFS honesty w.r.t. the base
-- statement:
--   Let $t$ be an eligible tenacity (odd, $t_m\le t<l_m$) and $U_t=\{u\in V:\mathrm{tenacity}(u)=t\}$. For every $v\in U_t$:
--
--   1. Every max level($v$) path contains a bridge of tenacity $t$.
--   2. The set $B(v)$ is a singleton; its element is $\mathrm{base}(v)$.
--   3. Let $b=\mathrm{base}(v)$. Every even level($v$) path is an even level($b$) path followed by an even level($b;v$) path, and every odd level($v$) path is an even level($b$) path followed by an odd level($b;v$) path; in both cases the second part lies in $B_{b,t}\cup\{b\}$.
--   4. Blossoms of tenacity $t$ with distinct bases are disjoint, and the family of blossoms of tenacity at most $t$ is laminar.
--   5. Let $p$ be an even level($u$) path from an unmatched vertex $f$ to a vertex $u$, let $w$ lie on $p$ with $\mathrm{tenacity}(w)=t$, and let $b=\mathrm{base}(w)$. Then $b$ lies on $p$, and $p[b\text{ to }w]$ is an even level($b;w$) path if its length is even and an odd level($b;w$) path if its length is odd.
--
--   This is the structure theorem behind the correctness proof of the Micali–Vazirani maximum matching algorithm: Statement 1 guarantees that processing bridges by tenacity finds every shortest alternating path, and Statements 2–5 make bases and nested blossoms well defined.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The hypothesis that $t$ is eligible implies $t_m<l_m$.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: b = base(v), the unique element of B(v) (Definitions 21, 29) → hypothesis IsBase M v b, i.e. baseSet M v = {b}, for every such b; reason: no junk value for base(v); together with Statement 2 / Corollary 2 it is the printed claim
--   - encoding: B_{b,t} by Definitions 22 and 31, union over basal v → one recursion blossom M b t on t, union over all w ∈ T_{b,t} ∪ {b}; reason: a non-basal w has an empty blossom, so the union is unchanged; at t = t_m it is Definition 22
--   - encoding: p[b to u], b before or after u on p (Definitions 7, 24, 33) → some q : G.Walk b u with IsSegmentFrom p q (p = p₁ q p₂ or p = p₁ q⁻¹ p₂); reason: on a simple path the segment exists and is unique when b, u lie on p
--   - reading: "a blossom B_{b,t}" / "the blossoms of tenacity t" → blossom M b t for b with IsBlossomBase M b t (b basal at stage t, tenacity b > t); reason: Definition 31 defines B_{b,t} only for a basal b with tenacity(b) > t; without the restriction a lower-stage base b has B_{b,t} = B_{b,t−2} nested in another blossom
--   - reading: "Let t be an eligible tenacity, Ut = {u ∈ V | tenacity(u) = t}, and v ∈ Ut. The following hold." → Statements 4 and 5, which do not mention v, are asserted for every eligible t, also when U_t = ∅; reason: Hypothesis 1 (p.2033) applies "each of the statements" to every tenacity in a range, and Definition 31 (p.2037) covers T_{b,t} = ∅; with U_t = ∅ Statement 5 is vacuous and Statement 4 concerns B_{b,t} = B_{b,t−2}; this is the stronger reading
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Theorem 3, p.2034

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_IsOddLevelPath
import Definitions.Def_MVBlossoms_IsMaxLevelPath
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_IsEligible
import Definitions.Def_MVBlossoms_IsBridge
import Definitions.Def_MVBlossoms_baseSet
import Definitions.Def_MVBlossoms_IsBase
import Definitions.Def_MVBlossoms_IsEvenLevelFromPath
import Definitions.Def_MVBlossoms_IsOddLevelFromPath
import Definitions.Def_MVBlossoms_IsBFSHonestWrt
import Definitions.Def_MVBlossoms_blossom
import Definitions.Def_MVBlossoms_IsBlossomBase
import Definitions.Def_MVBlossoms_IsLaminar
import Definitions.Def_MVBlossoms_blossomsUpTo

namespace MVBlossoms

/-- **Theorem 3.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Theorem 3, p.2034: "Let t be an eligible tenacity,
Ut = {u ∈ V | tenacity(u) = t}, and v ∈ Ut. The following hold.
Statement 1. Every max level(v) path contains a bridge of tenacity t.
Statement 2. The set B(v) is a singleton.
Statement 3. Let b = base(v). Then, every even level(v) (odd level(v)) path consists of an even
level(b) path followed by an even level(b;v) (odd level(b;v)) path, where the latter lies in
B_{b,t} ∪ {b}.
Statement 4. The blossoms of tenacity t are disjoint, and the set of blossoms of tenacity at most t
forms a laminar family.
Statement 5. Let p be an even level(u) path from unmatched vertex f to an arbitrary vertex u. Let
w ∈ p with tenacity(w) = t, and let b = base(w). Then, b also lies on p, and w is BFS honest on p
w.r.t. b."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). `t` is an eligible tenacity (`IsEligible`: odd,
`t_m ≤ t < l_m`). "b = base(v)" is `IsBase M v b` (`B(v) = {b}`), which Statement 2 shows exists.
"The blossoms of tenacity t" are `blossom M b t` for `b` with `IsBlossomBase M b t` (`b` basal at
stage `t` and `tenacity(b) > t`, Definition 31). Paths are simple walks; `p[b to w]` is read from
`b` whichever of `b`, `w` comes first on `p` (`IsSegmentFrom`). -/
theorem theorem_3 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching)
    (t : ℕ) (ht : IsEligible M t) :
    -- Statement 1
    (∀ v : V, tenacity M v = (t : ℕ∞) → ∀ (f : V) (p : G.Walk f v), IsMaxLevelPath M p →
      ∃ a b : V, s(a, b) ∈ p.edges ∧ IsBridge M a b ∧ edgeTenacity M a b = (t : ℕ∞)) ∧
    -- Statement 2
    (∀ v : V, tenacity M v = (t : ℕ∞) → ∃ b : V, baseSet M v = {b}) ∧
    -- Statement 3
    (∀ v : V, tenacity M v = (t : ℕ∞) → ∀ b : V, IsBase M v b → ∀ (f : V) (p : G.Walk f v),
      (IsEvenLevelPath M p → ∃ (p₁ : G.Walk f b) (q : G.Walk b v), p = p₁.append q ∧
        IsEvenLevelPath M p₁ ∧ IsEvenLevelFromPath M q ∧
        ∀ x ∈ q.support, x ∈ blossom M b t ∨ x = b) ∧
      (IsOddLevelPath M p → ∃ (p₁ : G.Walk f b) (q : G.Walk b v), p = p₁.append q ∧
        IsEvenLevelPath M p₁ ∧ IsOddLevelFromPath M q ∧
        ∀ x ∈ q.support, x ∈ blossom M b t ∨ x = b)) ∧
    -- Statement 4
    ((∀ b b' : V, IsBlossomBase M b t → IsBlossomBase M b' t → b ≠ b' →
        Disjoint (blossom M b t) (blossom M b' t)) ∧
      IsLaminar (blossomsUpTo M t)) ∧
    -- Statement 5
    (∀ (u f : V) (p : G.Walk f u), IsEvenLevelPath M p → ∀ w ∈ p.support,
      tenacity M w = (t : ℕ∞) → ∀ b : V, IsBase M w b →
        b ∈ p.support ∧ IsBFSHonestWrt M p w b) := by sorry

end MVBlossoms
