-- Prove2me | Theorems.Thm_GlobalTheory_NonGenericLocalCheck_img_one
-- name    : GlobalTheory.NonGenericLocalCheck.img_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:57:03.795365+00:00
-- url     : https://prove2.me/theorems/cf59275c-c354-46bf-80b6-437e9d6113cb
-- title:
--   Non Generic Local Check: img one
-- statement:
--   The Non Generic Local Check construction uses the img one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/TransversalityLocal/FramePairFixatorUnitaryAndFixesFrame.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/TransversalityLocal/FramePairFixatorUnitaryAndFixesFrame.lean#L51-L58

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
variable {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem GlobalTheory.NonGenericLocalCheck.img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by sorry
