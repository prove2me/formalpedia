-- Prove2me | Theorems.Thm_MasulloGRH_continuous_projTensor_map_left
-- name    : MasulloGRH.continuous_projTensor_map_left
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:39:46.384252+00:00
-- url     : https://prove2.me/theorems/ea1c054a-cb39-466c-8a76-46b05f00da04
-- title:
--   Continuity of tensoring on the projective tensor product
-- statement:
--   Tensoring a continuous complex linear map in the first factor with the identity in the second factor gives a continuous map for the projective tensor topologies. This follows from their universal property for the canonical joint bilinear map.
-- source:
--   Functoriality of the projective and injective tensor topologies defined in Masullo, The Music of the Primes, frozen 20 November 2026 draft, Appendix C, §C.2.3 and Definition C.2.4.1. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex
open TensorProduct
universe u

namespace MasulloGRH

theorem continuous_projTensor_map_left (F G H : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] (f : F →L[ℂ] G) :
    @Continuous (F ⊗[ℂ] H) (G ⊗[ℂ] H) (projTensorTopology F H) (projTensorTopology G H)
      (TensorProduct.map f.toLinearMap (LinearMap.id : H →ₗ[ℂ] H)) := by sorry

end MasulloGRH
