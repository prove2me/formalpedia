-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameLift_core
-- name    : GlobalTheory.HL.FrameLift.core
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:39:21.219128+00:00
-- url     : https://prove2.me/theorems/864ab1e9-0cea-4c6c-ad1a-11e4b0be0925
-- title:
--   Frame Lift: core
-- statement:
--   The Frame Lift construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualLatticeUnipotentTranslateStandard.lean#L143-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualLatticeUnipotentTranslateStandard.lean#L143-L215

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

theorem GlobalTheory.HL.FrameLift.core [IsNoetherianRing L.O] (Λ : Submodule L.O S.V) (hfg : Λ.FG)
    (hsd : ∀ y, (∀ x ∈ Λ, hf L S.Hm x y ∈ L.O) ↔ y ∈ Λ) (hg : ∀ b, g b ∈ Λ) (hgs : ∀ j, gs j ∈ Λ)
    (c : S.V) (hc : c ∈ Λ) (hc' : ∀ b, hf L S.Hm (g b) c = if b = Fin.last r then 1 else 0) :
    ∃ A, S.IsInner g gs A ∧ Λ = S.stdLat g gs A := by sorry
