-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameStab_hf_sum
-- name    : GlobalTheory.HL.FrameStab.hf_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:10:16.552358+00:00
-- url     : https://prove2.me/theorems/a7b6b329-1ada-4a00-b288-3794779fcf7e
-- title:
--   Frame Stab: hf sum
-- statement:
--   The Frame Stab construction uses the hf sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCommonStabiliserEqPairingMatrixStabiliser.lean#L27-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCommonStabiliserEqPairingMatrixStabiliser.lean#L27-L45

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.FrameStab.hf_sum (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι κ : Type} [Fintype ι]
    [Fintype κ] (a : ι → E) (b : κ → E) (x : ι → Fin n → E) (y : κ → Fin n → E) :
    hf L Hm (∑ i, a i • x i) (∑ j, b j • y j) = ∑ i, ∑ j, a i * L.cj (b j) * hf L Hm (x i) (y j) := by sorry
