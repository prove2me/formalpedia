-- Prove2me | Theorems.Thm_FullFormalization_theorem_A_attainment
-- name    : FullFormalization.theorem_A_attainment
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T06:53:06.493673+00:00
-- url     : https://prove2.me/theorems/fb46474c-bad2-4a81-89ca-9a8beb30ace7
-- title:
--   Attainment of τ_N by the one-dimensional Huber function
-- statement:
--   The existence (lower-bound) half of Theorem A, in the normalised vocabulary of §1: there is a `NormalizedAtZero` function whose normalised excess loss at the NAG output is exactly $\tau_N$.
--
--   Take the one-dimensional Huber function with half-width $c = R/(2d_N+1)$, i.e. $f(x) = x^2/2$ for $|x| \le c$ and $f(x) = c|x| - c^2/2$ for $|x| \ge c$, where $d_N = N(N+7)/8$ and $R > 0$ is the radius. Then $f$ is `NormalizedAtZero` and
--
--   $$\frac{f(x_N) - f(0)}{R^2} = \frac{2}{N^2 + 7N + 4} = \tau_N,$$
--
--   with $x_N$ the rational-momentum Nesterov output of $f$ started at $R$ and $f(0) = f^\star = 0$.
--
--   This shows that the upper bound (19.1) is attained, hence cannot be improved. It is source §20 rewritten in the `NormalizedAtZero` vocabulary, i.e. `Huber1D.huber_attainment` / `huber_final_value`.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §20 (matching lower bound), eq. (20.1)-(20.4); Lean: FullFormalization.TheoremA lines 477-494

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
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_sub_pred
import Theorems.Thm_FullFormalization_d_succ_sub
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_deriv_huber
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
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagX_succ
import Theorems.Thm_FullFormalization_nagX_succ_prime
import Theorems.Thm_FullFormalization_nagY_succ
import Theorems.Thm_FullFormalization_nagY_succ_one
import Theorems.Thm_FullFormalization_tau_eq_inv
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











end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FullFormalization.theorem_A_attainment (N : ℕ) (hN : 1 ≤ N) {R : ℝ} (hR : 0 < R) :
    ∃ f : ℝ → ℝ, NormalizedAtZero f ∧
      (f (nagX f 1 R N) - f 0) / R ^ 2 = tau N := by sorry
