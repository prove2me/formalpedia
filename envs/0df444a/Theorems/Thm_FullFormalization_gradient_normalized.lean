-- Prove2me | Theorems.Thm_FullFormalization_gradient_normalized
-- name    : FullFormalization.gradient_normalized
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:52:18.971991+00:00
-- url     : https://prove2.me/theorems/69e0ef18-55e0-4c5a-8e0b-a9fe76cadb85
-- title:
--   Gradient of the normalised function (32.1)
-- statement:
--   Let $f : E \to \mathbb{R}$ be differentiable, let $L, R > 0$ and let $x^\star, y \in E$. The normalised function $z \mapsto \bigl(f(x^\star + R z) - f(x^\star)\bigr)/(L R^2)$ has gradient
--   $$\nabla_y\!\left(\frac{f(x^\star + R\, y) - f(x^\star)}{L R^2}\right) = \frac{1}{L R}\, \nabla f(x^\star + R\, y).$$
--   Here $R$ is the radius and $L$ the smoothness constant, and the formula is (32.1) read backwards: it is the chain-rule consequence of the change of variable $x = x^\star + R y$ that carries a general instance to the normalised one ($L = 1$, $x^\star = 0$). It is the tool that transports gradient information between the two settings in the scaling step of Theorem A.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §32, eq. (32.1) read backwards; Lean: FullFormalization.TheoremA lines 274-314

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
import Theorems.Thm_FullFormalization_comp_smul_one
import Theorems.Thm_FullFormalization_toDual_smul_real

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

theorem FullFormalization.gradient_normalized {f : E → ℝ} (hd : Differentiable ℝ f) {L R : ℝ} (hL : 0 < L)
    (hR : 0 < R) (xstar y : E) :
    ∇ (fun z : E => (1 / (L * R ^ 2)) * (f (xstar + R • z) - f xstar)) y
      = (1 / (L * R)) • ∇ f (xstar + R • y) := by sorry
