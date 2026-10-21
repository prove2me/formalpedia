-- Prove2me | Theorems.Thm_ModernConvex_EllipsoidMethod_termination_gives_solution
-- name    : ModernConvex.EllipsoidMethod.termination_gives_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:10.102169+00:00
-- url     : https://prove2.me/theorems/a8d769f9-b68d-4af8-bac1-93a8e6114a08
-- title:
--   2∗ — if the ellipsoid method terminates, its result is a feasible ε-solution
-- statement:
--   Let $n \ge 2$ and consider the convex program $\min\{f(x) : x \in X\}$ in $\mathbb R^n$ under assumption A: $f$ is convex on $\mathbb R^n$, $X$ is closed, bounded and convex with nonempty interior, $r, R > 0$, $X$ lies in the ball $E_0 = \{\|x\|_2 \le R\}$ and contains a Euclidean ball of radius $r$. Run the ellipsoid method with accuracy $\epsilon > 0$, a separation oracle for $X$ and a first order oracle for $f$.
--
--   If the method terminates at some step $t$ (by a zero subgradient or by the test (5.2.17)), then its result $\widehat x$ is well defined (in the second case: at least one of the steps $1, \dots, t$ was productive) and is a feasible $\epsilon$-solution:
--   $$\widehat x \in X \quad\text{and}\quad f(\widehat x) - \min_X f \le \epsilon.$$
--
--   This is the accuracy half of Theorem 5.2.1; it does not depend on how many steps were made.
--
--   **Formalization Note** "$f(\widehat x) - \min_X f \le \epsilon$" is stated as $f(\widehat x) - f(y) \le \epsilon$ for every $y \in X$, which is equivalent because the minimum is attained ($X$ is compact and $f$ continuous). The result of the method has type `Option`; "well defined" is the clause that it is `some x̂`.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 350, claim 2∗ (proof of Theorem 5.2.1)

import Mathlib
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod

open Matrix MeasureTheory

namespace ModernConvex.EllipsoidMethod

/-- Ben-Tal–Nemirovski, p. 350, claim 2∗ in the proof of Theorem 5.2.1. Let the ellipsoid
method with accuracy `ε > 0` be applied to (5.2.9) of dimension `n ≥ 2` under assumption A,
with a separation oracle for `X` and a first order oracle for `f`. If the method terminates at
some step `t`, then its result `x̂` is well defined and is a feasible `ε`-solution:
`x̂ ∈ X` and `f(x̂) − min_X f ≤ ε`. -/
theorem termination_gives_solution {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (result : Option (Fin n → ℝ)) (hterm : TerminatesAt sep O R r ε t result) :
    ∃ xhat : Fin n → ℝ, result = some xhat ∧ xhat ∈ X ∧ ∀ y ∈ X, f xhat - f y ≤ ε := by sorry

end ModernConvex.EllipsoidMethod
