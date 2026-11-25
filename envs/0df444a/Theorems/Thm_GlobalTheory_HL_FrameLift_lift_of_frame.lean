-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameLift_lift_of_frame
-- name    : GlobalTheory.HL.FrameLift.lift_of_frame
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:35.543433+00:00
-- url     : https://prove2.me/theorems/1972786a-74c3-40fe-85cf-0bdfe6e6bc26
-- title:
--   Frame Lift: lift of frame
-- statement:
--   The Frame Lift construction uses the lift of frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualLatticeUnipotentTranslateStandard.lean#L218-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualLatticeUnipotentTranslateStandard.lean#L218-L316

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameLift
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
  (iso : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
include gram dual iso

theorem GlobalTheory.HL.FrameLift.lift_of_frame [IsNonarchimedeanLocalField F] [CharZero F] (Λ : Submodule L.O S.V)
    (hΛ : IsSD L S.Hm Λ) (n : S.GLV) (hn : n ∈ S.Nof g)
    (hprim : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => n (g b))) :
    ∃ A, S.IsInner g gs A ∧ ∃ n₁ ∈ S.Nof g, (∀ b, n₁ (g b) = n (g b)) ∧ Λ = n₁ • S.stdLat g gs A := by sorry
