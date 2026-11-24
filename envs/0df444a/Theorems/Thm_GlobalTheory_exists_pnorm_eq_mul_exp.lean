-- Prove2me | Theorems.Thm_GlobalTheory_exists_pnorm_eq_mul_exp
-- name    : GlobalTheory.exists_pnorm_eq_mul_exp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:07.919777+00:00
-- url     : https://prove2.me/theorems/b321f1b7-2ca2-44e7-95e2-7d9ae487c807
-- title:
--   Global Theory: exists pnorm eq mul exp
-- statement:
--   The Global Theory construction uses the exists pnorm eq mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L185-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L185-L206

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.exists_pnorm_eq_mul_exp {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (y : Frame X.Ψ r) {t : ℝ}
    (hy : ∀ τ i, dmin X.Gm y τ i ≠ 0 ∧ |Real.log ‖dmin X.Gm y τ i‖| ≤ t) :
    ∃ s : ℝ, |s| ≤ t * ∑ τ, ∑ i, |(la τ i : ℝ)| ∧
      ∀ P : Frame X.Ψ r → ℂ, X.pnorm la P y = ‖P y‖ * Real.exp s := by sorry
