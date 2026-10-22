-- Prove2me | Theorems.Thm_FullFormalization_huber_of_abs_le
-- name    : FullFormalization.huber_of_abs_le
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:44:27.732281+00:00
-- url     : https://prove2.me/theorems/0758577b-0205-4e84-a81f-e9a9110c2692
-- title:
--   Huber function on its quadratic branch
-- statement:
--   The one-dimensional Huber function `huber c` of source (20.2) coincides with the quadratic $x^2/2$ on the central interval $|x| \le c$:
--
--   $$ \operatorname{huber}(c, x) = \frac{x^{2}}{2} \qquad \text{whenever } |x| \le c. $$
--
--   Here `c` is the cutoff parameter and `huber c` is the function defined by cases, $x^2/2$ for $|x| \le c$ and $c|x| - c^2/2$ for $|x| \ge c$; the hypothesis $|x| \le c$ selects the first branch.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §20, eq. (20.2); Lean: FullFormalization.Huber1D lines 124-125

-- Generated from F:/20261008/FullFormalization\FullFormalization\Huber1D.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.Huber1D

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 20
  (「定理 A 的 matching lower bound」, lines 1817-2046).

  The source fixes `L = 1`, `x⋆ = 0`, `x₀ = R > 0`, sets

      c = R / (2 d_N + 1)                                    (20.1)

  and defines the one-dimensional Huber function

      f x = x²/2            if |x| ≤ c
      f x = c |x| - c²/2    if |x| ≥ c                       (20.2)

  It then states (lines 1853-1858) that `f` is convex, differentiable, has a
  globally 1-Lipschitz gradient and has `0` as its unique minimizer, and proves
  the NAG trajectory identity

      x_j = R - d_j c                                        (20.3)

  together with the observation that the whole trajectory stays in the positive
  linear branch (`x_j ≥ c` for `j ≤ N`, source 20.2), whence

      (f(x_N) - f⋆) / R² = 2 / (N² + 7 N + 4)                (20.4)

  i.e. exactly `tau N` of `FullFormalization.Coefficients`.  This is the
  matching lower bound: the upper bound (19.1) is attained.

  ## Representation choices

  * The constant `c` is called `huberC` here: `d` is the coefficient sequence of
    `FullFormalization.Coefficients`, and `c` is used as a bound variable
    throughout the project, so a global `c` would be confusing.

  * `huber c : ℝ → ℝ` is stated for an arbitrary `c`; every property below
    carries the hypothesis `0 ≤ c` (or `0 < c`) that the source's `c`, being a
    quotient by the positive `2 d_N + 1`, always satisfies.

  * The gradient of `huber c` is the clipping `huberClamp c x = max (-c) (min c x)`
    of `x` to `[-c, c]`.  Its 1-Lipschitz property is `huberClamp_lipschitz`;
    it is monotone, which is how convexity of `huber c` is obtained (through
    `MonotoneOn.convexOn_of_deriv`).  Differentiability is proved by gluing the
    two branches at the kinks `±c`, where the one-sided derivatives agree.

  * **Index range of (20.3).**  The source writes `x_j = R - d_j c` for the
    iterates of the method.  The induction only ever queries `x_0, …, x_N`
    (the method stops at `x_N`), and it uses the branch hypothesis `x_j ≥ c`,
    which is *false* for `j > N`.  Accordingly `huber_traj` below is stated for
    `j ≤ N`, which is exactly the range on which (20.3) is true.  (For `N = 1`,
    `R = 1` one gets `c = 1/3`, `x_3 = -2/15` while `R - d_3 c = -1/4`: the
    unrestricted statement is false.)
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_Huber1D
import Definitions.Def_RationalNAG

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false

namespace FullFormalization

/-! ## Section 20.0: the Huber function -/









/-! ## Elementary values of `huber`, `huberClamp` and the coefficients -/

































/-! ## Elementary derivatives of the two branches -/







/-! ## Section 20, lines 1853-1858: the analytic properties of `huber`

The derivative is computed by gluing the two branches at the two kinks `±c`;
the one-sided derivatives agree there (both are `±c`), so the gluing goes
through `HasDerivWithinAt.union`. -/

















/-! ## Source line 1857-1858: `0` is the unique minimizer -/






/-! ## Section 20.1-20.2: the NAG trajectory -/







/-! ## Section 20.3: the attained value (20.4) -/







/-! ## Theorem A, lower bound: the Huber function attains the bound -/



end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false

theorem FullFormalization.huber_of_abs_le {c x : ℝ} (hx : |x| ≤ c) : huber c x = x ^ 2 / 2 := by sorry
