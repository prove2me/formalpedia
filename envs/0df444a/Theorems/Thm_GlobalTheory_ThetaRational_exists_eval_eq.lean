-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRational_exists_eval_eq
-- name    : GlobalTheory.ThetaRational.exists_eval_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:07:22.206269+00:00
-- url     : https://prove2.me/theorems/86acd038-4a59-4d78-870a-f79c0198e4a7
-- title:
--   Theta Rational: exists eval eq
-- statement:
--   The Theta Rational construction uses the exists eval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L367-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L367-L387

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]
omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]

theorem GlobalTheory.ThetaRational.exists_eval_eq {u : ι → E → ℂ}
    (hcl : ∀ y : ι → ℂ, (∀ F : MvPolynomial ι ℂ, (∀ e, MvPolynomial.eval (fun c => u c e) F = 0) →
      MvPolynomial.eval y F = 0) → ∃ e, y = fun c => u c e)
    (χ : Algebra.adjoin ℂ (Set.range u) →ₐ[ℂ] ℂ) : ∃ e, ∀ b, χ b = b.1 e := by sorry
