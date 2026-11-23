-- Prove2me | Theorems.Thm_NoHair_global_isometry_of_flat_end_developing_cover
-- name    : NoHair.global_isometry_of_flat_end_developing_cover
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:49:31.668314+00:00
-- url     : https://prove2.me/theorems/e132f0db-f0d4-44af-867d-d166c34e5f8b
-- title:
--   Global Euclidean isometry from the developing cover and its exterior sheet
-- statement:
--   Transitivity of the deck isometries on fibers and injectivity in the lifted far end force the projection to be bijective. Its length lifting then gives a global metric isometry. The smooth inverse exists by the local diffeomorphism property, and its differential preserves the Riemannian inner product.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.global_isometry_of_flat_end_developing_cover (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    (d : FlatEndDevelopingMap Q) :
    ∃ f : Q ≃ᵢ ADMPoint, ContMDiff 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f ∧
      ContMDiff 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f.symm ∧
      ∀ (q : Q) (v w : TangentSpace 𝓘(ℝ,ADMPoint) q),
        inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q v)
          (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q w) = inner ℝ v w := by sorry
