-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_NormOpen_eventually_isSquare_infinite
-- name    : GlobalTheory.QNorm.NormOpen.eventually_isSquare_infinite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:23:39.378804+00:00
-- url     : https://prove2.me/theorems/9f8886ef-1a42-458b-9850-adc1051ef498
-- title:
--   Norm Open: eventually is Square infinite
-- statement:
--   The Norm Open construction uses the eventually is Square infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOne.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOne.lean#L81-L96

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
omit [NumberField F]

theorem GlobalTheory.QNorm.NormOpen.eventually_isSquare_infinite (w : InfinitePlace F) :
    ∀ᶠ x in 𝓝 (1 : w.Completion), IsSquare x := by sorry
