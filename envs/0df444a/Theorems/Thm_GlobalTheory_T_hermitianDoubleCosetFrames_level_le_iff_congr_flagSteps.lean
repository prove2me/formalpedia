-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianDoubleCosetFrames_level_le_iff_congr_flagSteps
-- name    : GlobalTheory.T.hermitianDoubleCosetFrames_level_le_iff_congr_flagSteps
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:45:45.766118+00:00
-- url     : https://prove2.me/theorems/2a1b8b12-113e-47ce-9a3c-7563d110737d
-- title:
--   T: hermitian Double Coset Frames level le iff congr flag Steps
-- statement:
--   The T construction uses the hermitian Double Coset Frames level le iff congr flag Steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSte
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitianDoubleCosetFrames_level_le_iff_congr_flagSteps : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g g' : Fin (r + 1) → S.V), ∀ y ∈ S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1), ∀ j : ℕ, S.lev g g' (algebraMap F E S.th • y) ≤ j ↔ ∃ y₁ ∈ S.spanTo g j ⊔ S.spanTo g' j, y - y₁ ∈ S.Mof g g' := by sorry
