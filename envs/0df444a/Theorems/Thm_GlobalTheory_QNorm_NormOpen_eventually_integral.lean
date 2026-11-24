-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_NormOpen_eventually_integral
-- name    : GlobalTheory.QNorm.NormOpen.eventually_integral
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:05:03.548452+00:00
-- url     : https://prove2.me/theorems/05053c95-e7c8-484b-a52d-d66021228449
-- title:
--   Norm Open: eventually integral
-- statement:
--   The Norm Open construction uses the eventually integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOne.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOne.lean#L98-L102

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

theorem GlobalTheory.QNorm.NormOpen.eventually_integral :
    ∀ᶠ a in 𝓝 (1 : FiniteAdeleRing (𝓞 F) F), ∀ v, a v ∈ v.adicCompletionIntegers F := by sorry
