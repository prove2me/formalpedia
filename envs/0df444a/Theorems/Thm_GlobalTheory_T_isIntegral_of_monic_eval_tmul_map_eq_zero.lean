-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_of_monic_eval_tmul_map_eq_zero
-- name    : GlobalTheory.T.isIntegral_of_monic_eval_tmul_map_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:48:10.744954+00:00
-- url     : https://prove2.me/theorems/4dfab782-5fc3-4660-910c-6855840dcf93
-- title:
--   T: is Integral of monic eval tmul map eq zero
-- statement:
--   The T construction uses the is Integral of monic eval tmul map eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntegralOfFiniteBaseChangeImageStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntegralOfFiniteBaseChangeImageStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntegralOfFiniteBaseChangeImage
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntegralOfFiniteBaseChangeImageStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegral_of_monic_eval_tmul_map_eq_zero : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ (ω : L ⊗[F] K) (p : Polynomial (U ⊗[T] C)), p.Monic → p.eval₂ φ ω = 0 → IsIntegral U ω := by sorry
