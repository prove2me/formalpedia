-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_NormOpen_continuous_eval
-- name    : GlobalTheory.QNorm.NormOpen.continuous_eval
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:31:57.434348+00:00
-- url     : https://prove2.me/theorems/086aa4c8-7716-4c6a-866e-4722d0d002fe
-- title:
--   Norm Open: continuous eval
-- statement:
--   The Norm Open construction uses the continuous eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOne.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOne.lean#L104-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticFormIdeleValuesMemNhdsOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Topology
open GlobalTheory GlobalTheory.QNorm
open GlobalTheory.QNorm.NormOpen
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.QNorm.NormOpen.continuous_eval (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (fun a : FiniteAdeleRing (𝓞 F) F => a v) := by sorry
