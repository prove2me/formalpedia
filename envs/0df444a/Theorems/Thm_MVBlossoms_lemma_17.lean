-- Prove2me | Theorems.Thm_MVBlossoms_lemma_17
-- name    : MVBlossoms.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:45:27.797982+00:00
-- url     : https://prove2.me/theorems/22069181-4496-4e5f-8944-d24a8054d312
-- title:
--   Lemma 17 — the ends of a matched edge of eligible tenacity $t$ share their base and blossom
-- statement:
--   Let $t$ be an eligible tenacity and $(u,v)$ a matched edge with $\mathrm{tenacity}(u,v)=t$. Then $u$ and $v$ have the same base $b$, and both belong to the blossom $B_{b,t}$.
--
--   This extends Corollary 3 from $t_m$ to every eligible tenacity.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The hypothesis that $t$ is eligible implies $t_m<l_m$.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: b = base(v), the unique element of B(v) (Definitions 21, 29) → conclusion ∃ b, IsBase M u b ∧ IsBase M v b, where IsBase M x b is baseSet M x = {b}; reason: no junk value for base(·); "have the same base, say b" asserts that both bases exist and coincide
--   - encoding: B_{b,t} by Definitions 22 and 31, union over basal v → one recursion blossom M b t on t, union over all w ∈ T_{b,t} ∪ {b}; reason: a non-basal w has an empty blossom, so the union is unchanged; at t = t_m it is Definition 22
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 17, p.2037

import Mathlib
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_IsEligible
import Definitions.Def_MVBlossoms_IsBase
import Definitions.Def_MVBlossoms_blossom

namespace MVBlossoms

/-- **Lemma 17.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 17, p.2037: "Let (u, v) be a matched edge of tenacity t.
Then, u and v have the same base, say b, and both belong to the same blossom of tenacity t, namely
B_{b,t}."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). `t` is an eligible tenacity (§8.3, p.2033: the induction runs over
eligible `t`), which also gives `t_m < l_m`. -/
theorem lemma_17 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching)
    (t : ℕ) (ht : IsEligible M t)
    (u v : V) (huv : s(u, v) ∈ M.edgeSet) (hten : edgeTenacity M u v = (t : ℕ∞)) :
    ∃ b : V, IsBase M u b ∧ IsBase M v b ∧ u ∈ blossom M b t ∧ v ∈ blossom M b t := by sorry

end MVBlossoms
