-- Prove2me | Theorems.Thm_Gribov_reduced_gauge_group_homotopy_nontrivial
-- name    : Gribov.reduced_gauge_group_homotopy_nontrivial
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T14:17:12.752226+00:00
-- url     : https://prove2.me/theorems/8d72f4dc-6701-4a98-b814-5af809d2faca
-- title:
--   Theorem 3: $\pi_j(\overline{\mathcal{G}}) \neq 0$ for some $j$
-- statement:
--   **Theorem 3 of Singer's paper.** For $M = S^3$ or $M = S^4$ and $N \ge 2$, the reduced gauge group $\overline{\mathcal{G}} = C(M, SU(N))/Z_N$ of the trivial $SU(N)$-bundle has a nonvanishing homotopy group in some degree $j \ge 1$:
--   $$\exists\, j \ge 1 : \pi_j(\overline{\mathcal{G}}) \neq 0 .$$
--   Singer obtains this from Theorem 5 and the exact sequences $0 \to Z_N \to \mathcal{G} \to \overline{\mathcal{G}} \to 0$ and $0 \to \mathcal{G}_m \to \mathcal{G} \to SU(N) \to 0$: for $M = S^3$, $\pi_0(\mathcal{G}_m) \cong \pi_3(SU(N)) = \mathbb{Z}$ forces $\pi_1(\overline{\mathcal{G}}) \neq 0$; for $M = S^4$ and $N > 2$ the same conclusion holds; for $SU(2)$ over $S^4$, either $\pi_2(\overline{\mathcal{G}})$ or $\pi_3(\overline{\mathcal{G}})$ is nonzero. This nonvanishing is what obstructs a global gauge.
-- source:
--   I. M. Singer, Some Remarks on the Gribov Ambiguity, Commun. Math. Phys. 60 (1978) 7-12, https://doi.org/10.1007/BF01609471, p. 9, Theorem 3 (proof completed p. 10)

import Definitions.Def_gribov_gauge_group

open scoped Topology

namespace Gribov

/-- Singer, Theorem 3: some homotopy group of the reduced gauge group is nonzero. -/
theorem reduced_gauge_group_homotopy_nontrivial (r N : ℕ) (hr : r = 3 ∨ r = 4)
    (hN : 2 ≤ N) :
    ∃ j : ℕ, Nontrivial (π_ (j + 1) (ReducedGaugeGroup (Sphere r) N) 1) := by sorry

end Gribov
