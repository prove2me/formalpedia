-- Prove2me | Theorems.Thm_Gribov_no_continuous_gauge_fixing
-- name    : Gribov.no_continuous_gauge_fixing
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T14:15:12.084844+00:00
-- url     : https://prove2.me/theorems/08172c4e-0a8b-4085-b98b-20015bef3e4f
-- title:
--   Singer's Corollary 4: no continuous gauge exists
-- statement:
--   **Corollary 4 of Singer's paper.** Let $r = 3$ or $r = 4$ and let $N \ge 2$, and let
--   $$\overline{\mathcal{G}} = C(S^r, SU(N))/Z_N$$
--   be the reduced gauge group of the trivial $SU(N)$-bundle over the sphere $S^r$. Let $A$ be any topological space carrying a continuous action of $\overline{\mathcal{G}}$ which is *principal* (the action is free and the division map of pairs lying on a common orbit is continuous) and *weakly contractible* ($A$ is nonempty and all its homotopy groups vanish).
--
--   Then there is no gauge fixing: no continuous map
--   $$s : A/\overline{\mathcal{G}} \longrightarrow A$$
--   satisfies $p \circ s = \mathrm{id}$ for the canonical projection $p$.
--
--   In the paper, Theorems 1 and 2 show that the space $\mathfrak{R}$ of irreducible connections over $S^3$ or $S^4$ is exactly such a space, so this contains Corollary 4 for it: no continuous choice of one vector potential on each gauge orbit exists, in any gauge. The space of connections itself is not constructed here (Mathlib has no such space), which is why the statement quantifies over an abstract space with those two properties; the class is nonempty, e.g. the total space of a universal $\overline{\mathcal{G}}$-bundle belongs to it.
-- source:
--   I. M. Singer, Some Remarks on the Gribov Ambiguity, Commun. Math. Phys. 60 (1978) 7-12, https://doi.org/10.1007/BF01609471, p. 9, Corollary 4 (with Theorems 1 and 2, p. 8-9)

import Definitions.Def_gribov_gauge_group
import Definitions.Def_gribov_gauge_fixing

open scoped Topology

namespace Gribov

/-- Singer, Corollary 4: no continuous gauge exists. -/
theorem no_continuous_gauge_fixing (r N : ℕ) (hr : r = 3 ∨ r = 4) (hN : 2 ≤ N)
    (A : Type) [TopologicalSpace A]
    [MulAction (ReducedGaugeGroup (Sphere r) N) A]
    [ContinuousSMul (ReducedGaugeGroup (Sphere r) N) A]
    (hprin : IsPrincipalAction (ReducedGaugeGroup (Sphere r) N) A)
    (hwc : IsWeaklyContractible A) :
    ¬ ∃ s : OrbitSpace (ReducedGaugeGroup (Sphere r) N) A → A,
        IsGaugeFixing (ReducedGaugeGroup (Sphere r) N) A s := by sorry

end Gribov
