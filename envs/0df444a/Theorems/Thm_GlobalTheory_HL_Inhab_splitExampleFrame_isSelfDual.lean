-- Prove2me | Theorems.Thm_GlobalTheory_HL_Inhab_splitExampleFrame_isSelfDual
-- name    : GlobalTheory.HL.Inhab.splitExampleFrame_isSelfDual
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:39:40.523841+00:00
-- url     : https://prove2.me/theorems/5082dd6f-f69c-4420-9791-a549cbe500f0
-- title:
--   Inhab: split Example Frame is Self Dual
-- statement:
--   The Inhab construction uses the split Example Frame is Self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L570-L573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L570-L573

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.Inhab.splitExampleFrame_isSelfDual (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    IsSD L (toyG L hE ϖ hϖ m).Hm (stdLat L _) := by sorry
