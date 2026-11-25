-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGauss_fderiv_translate
-- name    : GlobalTheory.ThetaGauss.fderiv_translate
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:48:04.289393+00:00
-- url     : https://prove2.me/theorems/176c0200-aaaa-41af-b066-6f3cc75d0829
-- title:
--   Theta Gauss: fderiv translate
-- statement:
--   The Theta Gauss construction uses the fderiv translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L375-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L375-L390

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}

theorem GlobalTheory.ThetaGauss.fderiv_translate {f p : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (hp : Differentiable ℂ p) (a v : Fin g → ℂ) (j : (Fin g → ℂ) → ℂ) (l : ℂ)
    (hj : ∀ z (t : ℂ), j (z + t • v) = j z * Complex.exp (t * l))
    (h : ∀ z, f (z + a) = j z * p z) (z : Fin g → ℂ) :
    fderiv ℂ f (z + a) v = j z * (fderiv ℂ p z v + l * p z) := by sorry
