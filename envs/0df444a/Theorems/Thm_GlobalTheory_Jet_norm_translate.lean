-- Prove2me | Theorems.Thm_GlobalTheory_Jet_norm_translate
-- name    : GlobalTheory.Jet.norm_translate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:12:16.969667+00:00
-- url     : https://prove2.me/theorems/f61747a6-a0a7-443c-8497-769f31a8d28d
-- title:
--   Jet: norm translate
-- statement:
--   The Jet construction uses the norm translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L118-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L118-L134

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

theorem GlobalTheory.Jet.norm_translate (q : ℕ) (y : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ)
    (v : EuclideanSpace ℂ ι) :
    ‖cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y)‖ ^ 2 *
        Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) =
      ‖F (v - y)‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v - y‖ ^ 2) := by sorry
