-- Prove2me | Theorems.Thm_GlobalTheory_CurveProductSmooth_JointlySmooth_translate
-- name    : GlobalTheory.CurveProductSmooth.JointlySmooth.translate
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:28.641212+00:00
-- url     : https://prove2.me/theorems/49f7535d-f4d2-411a-bfeb-730686b34845
-- title:
--   Jointly Smooth: translate
-- statement:
--   The Jointly Smooth construction uses the translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlongCurveProductsStable.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlongCurveProductsStable.lean#L19-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlongCurveProductsStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory
open GlobalTheory.CurveProductSmooth
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G)
variable {ρ A e}

theorem GlobalTheory.CurveProductSmooth.JointlySmooth.translate {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) (m : List (P × (E → ℝ)))
    (hm : ∀ a ∈ m, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    JointlySmooth ρ A e fun t => ρ (m.map fun a => e a.1 (a.2 t)).prod (Φ t) := by sorry
