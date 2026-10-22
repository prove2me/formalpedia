-- Prove2me | Theorems.Thm_FullFormalization_theorem_A_sup
-- name    : FullFormalization.theorem_A_sup
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T07:34:59.825869+00:00
-- url     : https://prove2.me/theorems/6fba9b01-2c58-4d53-9dff-14f835c51460
-- title:
--   Theorem A: supremum of the normalized excess loss equals τ_N
-- statement:
--   The literal supremum form of Theorem A: over all `NormalizedAtZero` functions, the normalised excess loss at the rational-momentum Nesterov output $x_N$ has supremum exactly $\tau_N$.
--
--   $$\sup\Big\{\, \frac{f(x_N) - f(0)}{R^2} \;:\; f \text{ is } \texttt{NormalizedAtZero} \,\Big\} = \tau_N = \frac{2}{N^2 + 7N + 4},$$
--
--   where $R > 0$ is the radius of the normalised initial condition, $x_N$ the NAG output, $f(0) = f^\star$ the optimal value and $N \ge 1$ the step count.
--
--   The upper half of the supremum is `theorem_A_upper_normalized`, built on the master telescoping certificate (7.1) for $N \ge 2$ and the dedicated boundary certificate (18.1) for $N = 1$; the value $\tau_N$ is attained by `theorem_A_attainment`. Together with the pair form `theorem_A` the two statements are equivalent.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §17-20, eq. (17.1), (19.1), (20.4) and boxed statement (A); Lean: FullFormalization.TheoremA lines 522-542

-- Generated from F:/20261008/FullFormalization\FullFormalization\TheoremA.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.TheoremA

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`.
  Theorem A (source lines 17-56, boxed at line 3002) assembled from the pieces
  that are already verified elsewhere in this development.

  The three layers:

  * `nag_upper_bound_normalized` — (1.1)/(17.1) in the normalised setting
    `L = 1`, `x⋆ = 0`, `f⋆ = 0`, where the initial point is `r` and the radius is
    `‖r‖`: `F_N - f⋆ = F_N ≤ τ_N ‖r‖²`.  For `N ≥ 2` this is the master
    certificate (7.1) of section 12 — `CertificateIdentities` (9.1), (10.1),
    (11.1), (11.2) fed into `MasterCertificate.telescope` — combined with the
    nonnegativity of the interpolation residual (2.2), of the square terms
    (sections 14-16) and of the weights (section 13).  For `N = 1` it is the
    dedicated certificate (18.1) of section 18 (`NAGUpperBound.boundary_bound`),
    whose value `1/6` is exactly `τ_1`, so the two branches join without gap.

  * `theorem_A_upper` — the general `L, R` form (19.1)/(32.1).  Given an
    admissible `f` with optimiser `x⋆` and `‖x₀ - x⋆‖ ≤ R`, the normalised
    function is `f_N y = (f (x⋆ + R y) - f⋆)/(L R²)`, which is
    `NormalizedAtZero`; `Scaling.gradient_scaled` and `Scaling.differentiable_scaled`
    (with the local `gradient_normalized`/`gradient_const_add`) show that both
    NAG trajectories are related by `x_k = x⋆ + R · x_k^N` (proved directly, as
    in `Scaling.nag_pair_scaled`, but starting from the general `x₀`), and
    `nag_upper_bound_normalized` applied to `f_N` then gives the bound.

  * `theorem_A_attainment` / `theorem_A` / `theorem_A_sup` — the equality case of
    section 20: the one-dimensional Huber function (`Huber1D.huber_attainment`)
    is `NormalizedAtZero` and attains `τ_N` exactly.  **The supremum claim is
    stated in both forms**: `theorem_A_sup` is the literal `sSup` statement, and
    `theorem_A` is the equivalent pair "every admissible function satisfies the
    upper bound" ∧ "some admissible function attains it".  The pair form is the
    one used to *prove* the supremum (upper half + attained value), and the two
    forms are equivalent, so neither weakens the mathematics.
    (`theorem_A_attainment_admissible` records the same attainment in the
    source's own `Admissible`-class vocabulary.)

  **Scalar-multiplication pitfall** (hit three times earlier in this project):
  a bare `(1/2) • v` elaborates the numeral at type `ℕ`.  Every scalar in this
  file is written with an explicit `ℝ` ascription, e.g. `((1 : ℝ) / 2) • v`.

  Nothing is postulated: no `sorry`, `admit`, `axiom` or `unsafe`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_Huber1D
import Definitions.Def_NAGUpperBound
import Definitions.Def_Positivity
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling
import Definitions.Def_TheoremA
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
import Theorems.Thm_FullFormalization_convexOn_le_gradient
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_sub_pred
import Theorems.Thm_FullFormalization_d_succ_sub
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_deriv_huber
import Theorems.Thm_FullFormalization_descent_lemma
import Theorems.Thm_FullFormalization_differentiable_inner_const
import Theorems.Thm_FullFormalization_endpoint_identity
import Theorems.Thm_FullFormalization_gradient_inner_const
import Theorems.Thm_FullFormalization_gradient_sub
import Theorems.Thm_FullFormalization_gradient_sub_inner
import Theorems.Thm_FullFormalization_h_at_N
import Theorems.Thm_FullFormalization_h_last
import Theorems.Thm_FullFormalization_h_last_prime
import Theorems.Thm_FullFormalization_h_pos
import Theorems.Thm_FullFormalization_h_rec
import Theorems.Thm_FullFormalization_hasDerivAt_huber
import Theorems.Thm_FullFormalization_hasDerivAt_huber_pos
import Theorems.Thm_FullFormalization_hasDerivAt_linear
import Theorems.Thm_FullFormalization_hasDerivAt_neglinear
import Theorems.Thm_FullFormalization_hasDerivAt_sq_div_two
import Theorems.Thm_FullFormalization_huberC_le_traj
import Theorems.Thm_FullFormalization_huberC_mul
import Theorems.Thm_FullFormalization_huberC_pos
import Theorems.Thm_FullFormalization_huberC_sq
import Theorems.Thm_FullFormalization_huberC_sub
import Theorems.Thm_FullFormalization_huberClamp_lipschitz
import Theorems.Thm_FullFormalization_huberClamp_mono
import Theorems.Thm_FullFormalization_huberClamp_of_abs_lt
import Theorems.Thm_FullFormalization_huberClamp_of_c_le
import Theorems.Thm_FullFormalization_huberClamp_of_le_neg
import Theorems.Thm_FullFormalization_huberE_succ
import Theorems.Thm_FullFormalization_huberE_zero
import Theorems.Thm_FullFormalization_huber_algebra
import Theorems.Thm_FullFormalization_huber_convex
import Theorems.Thm_FullFormalization_huber_diff
import Theorems.Thm_FullFormalization_huber_final_value
import Theorems.Thm_FullFormalization_huber_in_linear_region
import Theorems.Thm_FullFormalization_huber_min
import Theorems.Thm_FullFormalization_huber_nonneg
import Theorems.Thm_FullFormalization_huber_of_abs_le
import Theorems.Thm_FullFormalization_huber_of_c_le
import Theorems.Thm_FullFormalization_huber_of_le_neg
import Theorems.Thm_FullFormalization_huber_smooth
import Theorems.Thm_FullFormalization_huber_traj
import Theorems.Thm_FullFormalization_huber_traj_pair
import Theorems.Thm_FullFormalization_huber_zero
import Theorems.Thm_FullFormalization_huber_zero_fun
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
import Theorems.Thm_FullFormalization_tau_eq_inv
import Theorems.Thm_FullFormalization_tau_one
import Theorems.Thm_FullFormalization_telescope
import Theorems.Thm_FullFormalization_terminal_identity
import Theorems.Thm_FullFormalization_theorem_A_attainment
import Theorems.Thm_FullFormalization_two_d_add_one

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### (1.1) / (17.1): the upper bound in the normalised setting -/



/-! ### Auxiliary gradient lemmas for the scaling (32.1) -/











/-! ### (19.1): the general `L, R` upper bound -/



/-! ### (20.4): the matching lower bound, and Theorem A -/





/-- Theorem A, upper half in normalised form: every `NormalizedAtZero` function
satisfies `(f(x_N) - f 0)/R² ≤ τ_N`.  This is `nag_upper_bound_normalized` with
the radius divided out. -/
theorem theorem_A_upper_normalized (N : ℕ) (hN : 1 ≤ N) {R : ℝ} (hR : 0 < R) :
    ∀ f : ℝ → ℝ, NormalizedAtZero f → (f (nagX f 1 R N) - f 0) / R ^ 2 ≤ tau N := by
  intro f hf
  have hb := nag_upper_bound_normalized hf R N hN
  rw [hf.value_at_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hR] at hb
  rw [div_le_iff₀ (pow_pos hR 2), hf.value_at_zero, sub_zero]
  exact hb





end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FullFormalization.theorem_A_sup (N : ℕ) (hN : 1 ≤ N) {R : ℝ} (hR : 0 < R) :
    sSup {v : ℝ | ∃ f : ℝ → ℝ, NormalizedAtZero f ∧
      v = (f (nagX f 1 R N) - f 0) / R ^ 2} = tau N := by sorry
