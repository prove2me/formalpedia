-- Prove2me | Theorems.Thm_MasulloRepair_nuclear_isometry_transport
-- name    : MasulloRepair.nuclear_isometry_transport
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T19:28:32.283825+00:00
-- url     : https://prove2.me/theorems/e3e17960-ec11-4568-bccd-74be27358de5
-- title:
--   Isometric transport preserves nuclearity and the Hilbert-space trace
-- statement:
--   Let $H,K$ be complete complex Hilbert spaces, let $U:H\to K$ be a linear isometric embedding, and let $T:H\to H$ be a nuclear bounded operator. Then
--   $$UTU^*\text{ is nuclear},\qquad \operatorname{Tr}_K(UTU^*)=\operatorname{Tr}_H(T).$$
--   The traces are the existing Hilbert-basis traces from `MasulloGRH_HilbertNuclear`, not newly defined transported functionals. The two Hilbert spaces may differ, and $U$ need not be onto.
--
--   This gives trace invariance for a common inner multiplier once the relevant operator is known to be nuclear. It does not establish nuclearity of any particular arithmetic operator.
-- source:
--   Auxiliary operator theorem for Yi's 'Actual global unit-shell increment at fixed incoming bandwidth', https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-a91427c0-0f6d-4e33-aa30-fe6dd8cddd02, step 5 ('Trace on the actual limiting projections'). This is an explicit general Hilbert-space lemma supporting the proposed repair, rather than a formalization of the full global trace formula. Trace input: https://prove2.me/theorems/465a23f4-910e-4e70-b797-ccb2aca78a12 (MasulloGRH.operatorTrace_of_nuclear_series).

import Definitions.Def_MasulloGRH_HilbertNuclear
import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option autoImplicit false
open MasulloGRH ContinuousLinearMap
open scoped InnerProductSpace

theorem MasulloRepair.nuclear_isometry_transport {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    IsNuclearOperator
      (U.toContinuousLinearMap ∘L T ∘L U.toContinuousLinearMap.adjoint) ∧
    operatorTrace (U.toContinuousLinearMap ∘L T ∘L U.toContinuousLinearMap.adjoint) =
      operatorTrace T := by sorry
