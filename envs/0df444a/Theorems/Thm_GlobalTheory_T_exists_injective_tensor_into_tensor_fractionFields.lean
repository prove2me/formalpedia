-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_injective_tensor_into_tensor_fractionFields
-- name    : GlobalTheory.T.exists_injective_tensor_into_tensor_fractionFields
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:41.836997+00:00
-- url     : https://prove2.me/theorems/b53b1103-f53d-41b2-bc07-2067b6a4debe
-- title:
--   T: exists injective tensor into tensor fraction Fields
-- statement:
--   The T construction uses the exists injective tensor into tensor fraction Fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatTensorEmbedsTensorFractionFieldsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatTensorEmbedsTensorFractionFieldsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatTensorEmbedsTensorFractionFields
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatTensorEmbedsTensorFractionFieldsStatement
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

theorem GlobalTheory.T.exists_injective_tensor_into_tensor_fractionFields : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Flat T U], ∃ φ : U ⊗[T] C →+* L ⊗[F] K, Function.Injective φ ∧ ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c := by sorry
