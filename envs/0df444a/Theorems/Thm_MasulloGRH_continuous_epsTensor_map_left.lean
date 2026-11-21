-- Prove2me | Theorems.Thm_MasulloGRH_continuous_epsTensor_map_left
-- name    : MasulloGRH.continuous_epsTensor_map_left
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:39:45.081934+00:00
-- url     : https://prove2.me/theorems/3443ff7e-74af-4fff-9318-def0e3c744fe
-- title:
--   Continuity of tensoring on the injective tensor product
-- statement:
--   Tensoring a continuous complex linear map in the first factor with the identity in the second factor gives a continuous map for the injective tensor topologies. The dual argument pulls each equicontinuous family back along the map, preserving the products that define uniform convergence.
-- source:
--   Functoriality of the projective and injective tensor topologies defined in Masullo, The Music of the Primes, frozen 20 November 2026 draft, Appendix C, §C.2.3 and Definition C.2.4.1. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex
open TensorProduct
universe u

namespace MasulloGRH

theorem continuous_epsTensor_map_left (F G H : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] (f : F →L[ℂ] G) :
    @Continuous (F ⊗[ℂ] H) (G ⊗[ℂ] H) (epsTensorTopology F H) (epsTensorTopology G H)
      (TensorProduct.map f.toLinearMap (LinearMap.id : H →ₗ[ℂ] H)) := by sorry

end MasulloGRH
