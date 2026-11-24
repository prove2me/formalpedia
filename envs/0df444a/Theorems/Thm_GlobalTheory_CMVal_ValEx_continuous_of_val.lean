-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_of_val
-- name    : GlobalTheory.CMVal.ValEx.continuous_of_val
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:10.230348+00:00
-- url     : https://prove2.me/theorems/49caaa21-0e79-4b09-9d9a-fba6de2e86f3
-- title:
--   Val Ex: continuous of val
-- statement:
--   The Val Ex construction uses the continuous of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L119-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L119-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
open WithZeroTopology

theorem GlobalTheory.CMVal.ValEx.continuous_of_val {K L : Type} [Field K] [Field L] [Valued K ℤᵐ⁰] [Valued L ℤᵐ⁰]
    (hK : Function.Surjective (Valued.v : K → ℤᵐ⁰)) (f : K →+* L) (hf : ∀ x, Valued.v (f x) = Valued.v x) :
    Continuous f := by sorry
