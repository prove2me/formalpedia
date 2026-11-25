-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_conn_changeFrame
-- name    : GlobalTheory.HermFrame.conn_changeFrame
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:33.997751+00:00
-- url     : https://prove2.me/theorems/21c04595-d772-40f6-94c2-a28ec592ed90
-- title:
--   Herm Frame: conn change Frame
-- statement:
--   The Herm Frame construction uses the conn change Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L510-L522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L510-L522

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n]
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}

theorem GlobalTheory.HermFrame.conn_changeFrame {A : E → Matrix n n ℂ} (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 1 A z) (hAu : IsUnit (A z).det) (hA0 : ∀ η, mdbar A z η = 0) (ξ : E) :
    conn (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) z ξ =
      (A z)⁻¹ * (conn H z ξ * A z + mdel A z ξ) := by sorry
