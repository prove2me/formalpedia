-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_NormOpen_eventually_isSquare_finite
-- name    : GlobalTheory.QNorm.NormOpen.eventually_isSquare_finite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:03:43.520429+00:00
-- url     : https://prove2.me/theorems/fc5aaab1-1900-420f-82d3-606cff0d80f6
-- title:
--   Norm Open: eventually is Square finite
-- statement:
--   The Norm Open construction uses the eventually is Square finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOne.lean#L16-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOne.lean#L16-L77

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

theorem GlobalTheory.QNorm.NormOpen.eventually_isSquare_finite (v : HeightOneSpectrum (𝓞 F)) :
    ∀ᶠ x in 𝓝 (1 : v.adicCompletion F), IsSquare x := by sorry
