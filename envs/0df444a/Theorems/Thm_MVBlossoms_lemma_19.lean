-- Prove2me | Theorems.Thm_MVBlossoms_lemma_19
-- name    : MVBlossoms.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:45:52.414229+00:00
-- url     : https://prove2.me/theorems/8043afc6-8c7d-463a-b6b4-420f4e6fe539
-- title:
--   Lemma 19 — a shortest even path meeting a blossom of tenacity $t$ crosses it in one shortest segment from the base
-- statement:
--   Let $t$ be an eligible tenacity and $p$ an even level($u$) path from an unmatched vertex $f$ to a vertex $u$, and let $B_{b,t}$ be a blossom of tenacity $t$ that meets $p$. Then $b$ lies on $p$, and there is a vertex $y\in p\cap B_{b,t}$ such that $p[b\text{ to }y]$
--
--   1. contains every vertex of $p$ that lies in $B_{b,t}\cup\{b\}$, and
--   2. is an even level($b;y$) path.
--
--   This extends Lemma 13 from $t_m$ to every eligible tenacity.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The hypothesis that $t$ is eligible implies $t_m<l_m$.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: B_{b,t} by Definitions 22 and 31, union over basal v → one recursion blossom M b t on t, union over all w ∈ T_{b,t} ∪ {b}; reason: a non-basal w has an empty blossom, so the union is unchanged; at t = t_m it is Definition 22
--   - encoding: p[b to u], b before or after u on p (Definitions 7, 24, 33) → some q : G.Walk b u with IsSegmentFrom p q (p = p₁ q p₂ or p = p₁ q⁻¹ p₂); reason: on a simple path the segment exists and is unique when b, u lie on p
--   - reading: "a blossom B_{b,t}" / "the blossoms of tenacity t" → blossom M b t for b with IsBlossomBase M b t (b basal at stage t, tenacity b > t); reason: Definition 31 defines B_{b,t} only for a basal b with tenacity(b) > t; without the restriction a lower-stage base b has B_{b,t} = B_{b,t−2} nested in another blossom
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 19, p.2038

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_IsEligible
import Definitions.Def_MVBlossoms_IsEvenLevelFromPath
import Definitions.Def_MVBlossoms_IsSegmentFrom
import Definitions.Def_MVBlossoms_blossom
import Definitions.Def_MVBlossoms_IsBlossomBase

namespace MVBlossoms

/-- **Lemma 19.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 19, p.2038: "Let p be an even level(u) path from unmatched
vertex f to an arbitrary vertex u such that there is a blossom B_{b,t} with p ∩ B_{b,t} ≠ ∅. Then,
the base of this blossom, b, also lies on p, and there is a vertex y ∈ (p ∩ B_{b,t}) such that
p[b to y] contains all vertices in p ∩ (B_{b,t} ∪ {b}) and p[b to y] is an even level(b;y) path."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). `t` is an eligible tenacity; "a blossom B_{b,t}" is `blossom M b t`
with `IsBlossomBase M b t` (`b` basal at stage `t`, `tenacity(b) > t`, Definition 31).
`p[b to y]` is `IsSegmentFrom`. -/
theorem lemma_19 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching)
    (t : ℕ) (ht : IsEligible M t)
    {f u : V} (p : G.Walk f u) (hp : IsEvenLevelPath M p)
    (b : V) (hb : IsBlossomBase M b t) (hmeet : ∃ x ∈ p.support, x ∈ blossom M b t) :
    b ∈ p.support ∧ ∃ y ∈ blossom M b t, ∃ q : G.Walk b y, IsSegmentFrom p q ∧
      (∀ x ∈ p.support, (x ∈ blossom M b t ∨ x = b) → x ∈ q.support) ∧
      IsEvenLevelFromPath M q := by sorry

end MVBlossoms
