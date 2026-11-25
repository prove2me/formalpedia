-- Prove2me | Theorems.Thm_GlobalTheory_HL_GoodClass_mem_cls
-- name    : GlobalTheory.HL.GoodClass.mem_cls
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:31:22.406993+00:00
-- url     : https://prove2.me/theorems/6ee5e964-25bb-4528-9d2d-598c99b57485
-- title:
--   Good Class: mem cls
-- statement:
--   The Good Class construction uses the mem cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitEntries.lean#L350-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitEntries.lean#L350-L356

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.GoodClass.mem_cls {L : LocE F E} {r k : ℕ} (S : Frames L r k) (hg : S.gg = false)
    (g g' : Fin (r + 1) → S.V) (p : S.FrP) {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hA : UpU A) (hA' : UpU A') (iA : IsIntM L A) (iA' : IsIntM L A')
    (h : ∀ j, p.1 j = ∑ i, A i j • g i) (h' : ∀ j, p.2 j = ∑ i, A' i j • g' i) :
    p ∈ S.frameCls g g' := by sorry
