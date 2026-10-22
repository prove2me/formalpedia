-- Prove2me | Theorems.Thm_FullFormalization_theoremAUpper_of_theorem_A
-- name    : FullFormalization.theoremAUpper_of_theorem_A
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T07:41:29.467987+00:00
-- url     : https://prove2.me/theorems/32c3effd-c5cc-4c23-9d5e-487783c776e8
-- title:
--   Theorem A's upper bound in portfolio vocabulary
-- statement:
--   `TheoremAUpper N E` is the portfolio form of Theorem A's upper bound: for every admissible instance on $E$ with $L>0$ and $R>0$, the rational-NAG loss is at most $\tau_N$,
--   $$\frac{f(x_{\text{NAG}}) - f^\star}{LR^2} \le \tau_N, \qquad \tau_N = \frac{2}{N^2+7N+4},$$
--   where $x_{\text{NAG}} = \mathrm{nagX}\ f\ L\ x_{\text{init}}\ N$ is the declared rational-NAG output and $f^\star$ the minimiser. It is exactly Theorem A's conclusion divided by the positive factor $LR^2$, which is the definition of the normalised loss $q_{\mathrm{NAG},N}$.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §17-§20 (Theorem A) and §22, eq. (22.1); Lean: FullFormalization.MainResults lines 32-51

-- Generated from F:/20261008/FullFormalization\FullFormalization\MainResults.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.MainResults

  Assembles the two headline results of the source document from the files that
  prove their halves, with **no hypothesis left standing in for a theorem**.

    * Theorem A — `auditable_full_proof_nag_and_five_algorithm_cn.md`, §17-§20:
      `TheoremA.theorem_A_upper`, `TheoremA.theorem_A_sup`;
    * Theorem B — §21-§32: `TheoremB.theoremB`, which up to now carried
      `TheoremAUpper N (GridSpace N)` as an explicit hypothesis because
      `TheoremA.lean` did not yet exist.

  This file supplies that hypothesis from `TheoremA.theorem_A_upper` and
  restates Theorem B without it.  Nothing is weakened: `TheoremAUpper` was
  always exactly the statement of Theorem A in the vocabulary of the portfolio
  file, and `TheoremB.theoremB`'s own docstring says so.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_CommonExtremizer
import Definitions.Def_FunctionClass
import Definitions.Def_GradientStrategies
import Definitions.Def_GridRefine
import Definitions.Def_HiddenDirection
import Definitions.Def_Huber1D
import Definitions.Def_LiftedHuber
import Definitions.Def_NAGUpperBound
import Definitions.Def_PortfolioDefinitions
import Definitions.Def_Positivity
import Definitions.Def_RandomSearch
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling
import Definitions.Def_TheoremA
import Definitions.Def_TheoremB
import Theorems.Thm_FullFormalization_D_diff
import Theorems.Thm_FullFormalization_D_diff_prime
import Theorems.Thm_FullFormalization_D_ne_zero
import Theorems.Thm_FullFormalization_D_pos
import Theorems.Thm_FullFormalization_D_succ
import Theorems.Thm_FullFormalization_D_zero_capital
import Theorems.Thm_FullFormalization_H_last_eq_d
import Theorems.Thm_FullFormalization_H_last_eq_d_prime
import Theorems.Thm_FullFormalization_H_pos_capital
import Theorems.Thm_FullFormalization_H_sub_H_pred
import Theorems.Thm_FullFormalization_H_sub_H_pred_prime
import Theorems.Thm_FullFormalization_H_zero
import Theorems.Thm_FullFormalization_Ival_nonneg
import Theorems.Thm_FullFormalization_Pbeta_pos
import Theorems.Thm_FullFormalization_Qbeta_pos
import Theorems.Thm_FullFormalization_a_eq
import Theorems.Thm_FullFormalization_a_last
import Theorems.Thm_FullFormalization_a_pos
import Theorems.Thm_FullFormalization_alpha_pos
import Theorems.Thm_FullFormalization_b_eq
import Theorems.Thm_FullFormalization_b_last_eq
import Theorems.Thm_FullFormalization_b_pos
import Theorems.Thm_FullFormalization_b_zero
import Theorems.Thm_FullFormalization_betaT_eq
import Theorems.Thm_FullFormalization_betaT_num_shift
import Theorems.Thm_FullFormalization_betaT_pos
import Theorems.Thm_FullFormalization_beta_eq_P
import Theorems.Thm_FullFormalization_beta_pos
import Theorems.Thm_FullFormalization_boundary_N_eq_one
import Theorems.Thm_FullFormalization_boundary_bound
import Theorems.Thm_FullFormalization_comp_smul_one
import Theorems.Thm_FullFormalization_convexOn_le_gradient
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_sub_pred
import Theorems.Thm_FullFormalization_d_succ_sub
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_descent_lemma
import Theorems.Thm_FullFormalization_differentiable_inner_const
import Theorems.Thm_FullFormalization_differentiable_scaled
import Theorems.Thm_FullFormalization_endpoint_identity
import Theorems.Thm_FullFormalization_gradient_add_const
import Theorems.Thm_FullFormalization_gradient_congr
import Theorems.Thm_FullFormalization_gradient_const_add
import Theorems.Thm_FullFormalization_gradient_inner_const
import Theorems.Thm_FullFormalization_gradient_normalized
import Theorems.Thm_FullFormalization_gradient_scaled
import Theorems.Thm_FullFormalization_gradient_sub
import Theorems.Thm_FullFormalization_gradient_sub_inner
import Theorems.Thm_FullFormalization_h_at_N
import Theorems.Thm_FullFormalization_h_last
import Theorems.Thm_FullFormalization_h_last_prime
import Theorems.Thm_FullFormalization_h_pos
import Theorems.Thm_FullFormalization_h_rec
import Theorems.Thm_FullFormalization_hasFDerivAt_scaledArg
import Theorems.Thm_FullFormalization_initial_identity
import Theorems.Thm_FullFormalization_interior_identity
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagX_succ
import Theorems.Thm_FullFormalization_nagX_succ_prime
import Theorems.Thm_FullFormalization_nagX_zero
import Theorems.Thm_FullFormalization_nagY_succ
import Theorems.Thm_FullFormalization_nagY_succ_one
import Theorems.Thm_FullFormalization_nagY_zero
import Theorems.Thm_FullFormalization_nag_upper_bound_normalized
import Theorems.Thm_FullFormalization_scaledArg_add_smul
import Theorems.Thm_FullFormalization_scaledArg_apply
import Theorems.Thm_FullFormalization_scaled_apply
import Theorems.Thm_FullFormalization_tau_eq_inv
import Theorems.Thm_FullFormalization_tau_one
import Theorems.Thm_FullFormalization_tau_pos
import Theorems.Thm_FullFormalization_telescope
import Theorems.Thm_FullFormalization_terminal_identity
import Theorems.Thm_FullFormalization_theorem_A_upper
import Theorems.Thm_FullFormalization_toDual_smul_real
import Theorems.Thm_FullFormalization_two_d_add_one

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]







end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem FullFormalization.theoremAUpper_of_theorem_A (N : ℕ) (hN : 1 ≤ N) : TheoremAUpper N E := by sorry
