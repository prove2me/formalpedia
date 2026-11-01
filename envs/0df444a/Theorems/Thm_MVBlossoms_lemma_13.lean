-- Prove2me | Theorems.Thm_MVBlossoms_lemma_13
-- name    : MVBlossoms.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:46:06.119012+00:00
-- url     : https://prove2.me/theorems/d25a7831-326a-4a7c-a2c4-d999b02e46d7
-- title:
--   Lemma 13 — a shortest even path meeting a blossom of tenacity $t_m$ crosses it in one shortest segment from the base
-- statement:
--   Let $p$ be an even level($v$) path from an unmatched vertex $f$ to a vertex $v$, and let $B_{b,t_m}$ be a blossom of tenacity $t_m$ that meets $p$. Then the base $b$ lies on $p$, and there is a vertex $u\in p\cap B_{b,t_m}$ such that the subpath $p[b\text{ to }u]$ (read from $b$, which may come before or after $u$ on $p$)
--
--   1. contains every vertex of $p$ that lies in $B_{b,t_m}\cup\{b\}$, and
--   2. is an even level($b;u$) path.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: B_{b,t} by Definitions 22 and 31, union over basal v → one recursion blossom M b t on t, union over all w ∈ T_{b,t} ∪ {b}; reason: a non-basal w has an empty blossom, so the union is unchanged; at t = t_m it is Definition 22
--   - encoding: the blossom B_{b,t_m} → blossom M b t₀ with t₀ : ℕ and (t₀ : ℕ∞) = t_m; reason: t_m is finite under t_m < l_m; t₀ is that natural number
--   - encoding: p[b to u], b before or after u on p (Definitions 7, 24, 33) → some q : G.Walk b u with IsSegmentFrom p q (p = p₁ q p₂ or p = p₁ q⁻¹ p₂); reason: on a simple path the segment exists and is unique when b, u lie on p
--   - reading: "a blossom B_{b,t}" / "the blossoms of tenacity t" → blossom M b t for b with IsBlossomBase M b t (b basal at stage t, tenacity b > t); reason: Definition 31 defines B_{b,t} only for a basal b with tenacity(b) > t; without the restriction a lower-stage base b has B_{b,t} = B_{b,t−2} nested in another blossom
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 13, p.2032

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsEvenLevelFromPath
import Definitions.Def_MVBlossoms_IsSegmentFrom
import Definitions.Def_MVBlossoms_blossom
import Definitions.Def_MVBlossoms_IsBlossomBase

namespace MVBlossoms

/-- **Lemma 13.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 13, p.2032: "Let p be an even level(v) path from unmatched
vertex f to an arbitrary vertex v such that there is a blossom B_{b,tm} with p ∩ B_{b,tm} ≠ ∅.
Then, the base of this blossom, b, also lies on p, and there is a vertex u ∈ (p ∩ B_{b,tm}) such that
p[b to u] contains all the vertices of p ∩ (B_{b,tm} ∪ {b}) and p[b to u] is an even level(b;u)
path."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. `t₀ : ℕ` is `t_m`; "a blossom B_{b,tm}" is `blossom M b t₀`
with `IsBlossomBase M b t₀`. `p[b to u]` is the segment of `p` between `b` and `u` read from `b`
(`IsSegmentFrom`), whichever of the two comes first on `p`. -/
theorem lemma_13 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (t₀ : ℕ) (ht₀ : (t₀ : ℕ∞) = tm M)
    {f v : V} (p : G.Walk f v) (hp : IsEvenLevelPath M p)
    (b : V) (hb : IsBlossomBase M b t₀) (hmeet : ∃ x ∈ p.support, x ∈ blossom M b t₀) :
    b ∈ p.support ∧ ∃ u ∈ blossom M b t₀, ∃ q : G.Walk b u, IsSegmentFrom p q ∧
      (∀ x ∈ p.support, (x ∈ blossom M b t₀ ∨ x = b) → x ∈ q.support) ∧
      IsEvenLevelFromPath M q := by sorry

end MVBlossoms
