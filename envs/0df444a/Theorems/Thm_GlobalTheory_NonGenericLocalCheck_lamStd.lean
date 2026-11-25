-- Prove2me | Theorems.Thm_GlobalTheory_NonGenericLocalCheck_lamStd
-- name    : GlobalTheory.NonGenericLocalCheck.lamStd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:41:59.873503+00:00
-- url     : https://prove2.me/theorems/fd4a575a-4985-4058-86a9-8d367f63e6f7
-- title:
--   Non Generic Local Check: lam Std
-- statement:
--   The Non Generic Local Check construction uses the lam Std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/TransversalityLocal/FramePairFixatorUnitaryAndFixesFrame.lean#L440-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/TransversalityLocal/FramePairFixatorUnitaryAndFixesFrame.lean#L440-L454

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

theorem GlobalTheory.NonGenericLocalCheck.lamStd (c : F) : (frame M m c).LamStd (inn M m c) =
    Submodule.span M.L.O {v | ∀ i, v i ∈ M.L.O} := by sorry
