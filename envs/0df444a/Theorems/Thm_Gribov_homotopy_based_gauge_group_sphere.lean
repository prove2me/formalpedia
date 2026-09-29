-- Prove2me | Theorems.Thm_Gribov_homotopy_based_gauge_group_sphere
-- name    : Gribov.homotopy_based_gauge_group_sphere
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T14:15:51.385373+00:00
-- url     : https://prove2.me/theorems/1c1d1078-61fe-492e-bdaf-8631e4253d44
-- title:
--   Theorem 5: $\pi_j(\mathcal{G}_m) \cong \pi_{j+r}(SU(N))$ for $M = S^r$
-- statement:
--   **Theorem 5 of Singer's paper, sphere case.** For the trivial $SU(N)$-bundle over $S^r$ with base point the north pole $m$, let $\mathcal{G}_m$ be the group of continuous based gauge transformations, i.e. continuous $\varphi : S^r \to SU(N)$ with $\varphi(m) = I$, under pointwise multiplication and the compact-open topology. Then for every $j \ge 1$ there is a group isomorphism
--   $$\pi_j(\mathcal{G}_m) \;\cong\; \pi_{j+r}(SU(N)),$$
--   based at the identity on both sides. Singer states this as $\pi_j(\mathcal{G}_m) \cong \pi_{j+r}(SU(N))$ for $M = S^r$, obtained from the identification of $\mathcal{G}_m$ with the space of based maps $(M,m) \to (SU(N), I)$ together with $S^j \wedge S^r = S^{j+r}$.
-- source:
--   I. M. Singer, Some Remarks on the Gribov Ambiguity, Commun. Math. Phys. 60 (1978) 7-12, https://doi.org/10.1007/BF01609471, p. 10, Theorem 5 (second statement)

import Definitions.Def_gribov_gauge_group

open scoped Topology

namespace Gribov

/-- Singer, Theorem 5 (sphere case): `π_j(𝒢_m) ≅ π_{j+r}(SU(N))` for `M = S^r`. -/
theorem homotopy_based_gauge_group_sphere (r N j : ℕ) :
    Nonempty (π_ (j + 1) (BasedGaugeGroup (Sphere r) N (northPole r)) 1 ≃*
      π_ (j + 1 + r) (SU N) 1) := by sorry

end Gribov
