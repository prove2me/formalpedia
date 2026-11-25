-- Prove2me | Theorems.Thm_GlobalTheory_NonGenericLocalCheck_isTermOver
-- name    : GlobalTheory.NonGenericLocalCheck.isTermOver
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:45:27.955874+00:00
-- url     : https://prove2.me/theorems/8b1f4284-1bd4-54ab-9806-fa14f6343361
-- title:
--   Non Generic Local Check: is Term Over
-- statement:
--   The Non Generic Local Check construction uses the is Term Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/TransversalityLocal/FramePairFixatorUnitaryAndFixesFrame.lean#L468-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/TransversalityLocal/FramePairFixatorUnitaryAndFixesFrame.lean#L468-L497

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable (M) (m : ℕ)

theorem GlobalTheory.NonGenericLocalCheck.isTermOver : IsTermOver (pair M m) (datum M m) (term M m) := by sorry
