-- Prove2me | Theorems.Thm_GlobalTheory_DiscOver_hf_smull
-- name    : GlobalTheory.DiscOver.hf_smull
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:25:21.970874+00:00
-- url     : https://prove2.me/theorems/087ee223-998e-4126-a1f0-230dd3f115ff
-- title:
--   Disc Over: hf smull
-- statement:
--   The Disc Over construction uses the hf smull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardDiscriminantModuleIntegralOverlatticeSpan.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardDiscriminantModuleIntegralOverlatticeSpan.lean#L27-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardDiscriminantModuleIntegralOverlatticeSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DiscOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.DiscOver.hf_smull (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by sorry
