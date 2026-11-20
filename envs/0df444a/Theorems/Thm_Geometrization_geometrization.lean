-- Prove2me | Theorems.Thm_Geometrization_geometrization
-- name    : Geometrization.geometrization
-- status  : Open
-- author  : @korbonits
-- created : 2026-11-20T02:09:45.792222+00:00
-- url     : https://prove2.me/theorems/4983b601-6413-4281-badc-890f762c7fd6
-- title:
--   Geometrization Conjecture (Thurston; Perelman, Morgan–Tian)
-- statement:
--   Let $M$ be a closed, connected, orientable, prime smooth 3-manifold. Then $M$ contains a finite disjoint union $\Sigma$ of smoothly embedded 2-tori and Klein bottles such that every connected component $C$ of $M \setminus \Sigma$ admits a locally homogeneous Riemannian metric of finite volume. That is, $C$ is diffeomorphic to $\Gamma\backslash X$ for a homogeneous Riemannian 3-manifold $X$ and a discrete group $\Gamma$ of isometries acting freely, and $\operatorname{vol}(\Gamma\backslash X) < \infty$. The family $\Sigma$ may be empty, in which case $M$ itself carries such a metric.
-- source:
--   J. Morgan, G. Tian, The Geometrization Conjecture, Clay Mathematics Monographs 5, AMS 2014 (https://www.claymath.org/library/monographs/cmim05c.pdf); statement transcribed from its arXiv precursor, Morgan–Tian, Completion of the proof of the Geometrization Conjecture, https://arxiv.org/abs/0809.4040, p. 1, statement of the Geometrization Conjecture: "Any closed, orientable, prime 3-manifold M contains a disjoint union of embedded 2-tori and Klein bottles such that each connected component of the complement admits a locally homogeneous Riemannian metric of finite volume."

import Definitions.Def_Geometrization_Basic

open scoped Manifold ContDiff

namespace Geometrization

/-- **Geometrization Conjecture** (Morgan–Tian). Any closed, orientable, prime 3-manifold `M`
contains a disjoint union of embedded 2-tori and Klein bottles such that each connected component
of the complement admits a locally homogeneous Riemannian metric of finite volume. -/
theorem geometrization (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (hM : IsOrientable M) (hP : IsPrime M) :
    ∃ S : TorusKleinSystem M, ∀ U : TopologicalSpace.Opens M, ∀ x ∉ S.carrier,
      (U : Set M) = connectedComponentIn S.carrierᶜ x →
        AdmitsFiniteVolumeLocallyHomogeneousMetric U := by sorry

end Geometrization
