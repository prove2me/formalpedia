-- Prove2me | Theorems.Thm_GlobalTheory_Jet_norm_polyDeriv_le
-- name    : GlobalTheory.Jet.norm_polyDeriv_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:57.108055+00:00
-- url     : https://prove2.me/theorems/59728d2f-b2a8-4b9e-8292-975ab4615d9f
-- title:
--   Jet: norm poly Deriv le
-- statement:
--   The Jet construction uses the norm poly Deriv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L138-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L138-L186

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.Jet
variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']
variable {ι : Type} [Fintype ι]
open Classical

theorem GlobalTheory.Jet.norm_polyDeriv_le (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ)
    (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ v, ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ S) (P : MvPolynomial ι ℂ) (a : ℕ)
    (hP : P.IsHomogeneous a) :
    ‖polyDeriv P (fun i => EuclideanSpace.single i 1) F 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S *
        (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by sorry
