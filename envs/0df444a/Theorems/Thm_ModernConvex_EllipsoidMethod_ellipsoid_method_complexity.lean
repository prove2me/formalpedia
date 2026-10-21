-- Prove2me | Theorems.Thm_ModernConvex_EllipsoidMethod_ellipsoid_method_complexity
-- name    : ModernConvex.EllipsoidMethod.ellipsoid_method_complexity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:02.493331+00:00
-- url     : https://prove2.me/theorems/5b069264-aa87-4acc-837e-a5ba48081917
-- title:
--   Theorem 5.2.1 — the ellipsoid method finds a feasible ε-solution within N(ε) steps
-- statement:
--   Let $n \ge 2$ and consider the convex program
--   $$\min_x\{f(x) : x \in X \subset \mathbb R^n\}$$
--   where $f : \mathbb R^n \to \mathbb R$ is convex and $X$ is a closed, bounded, convex set with nonempty interior that contains a Euclidean ball of a given radius $r > 0$ and is contained in the ball $E_0 = \{x \mid \|x\|_2 \le R\}$ of a given radius $R > 0$. Apply the ellipsoid method (definition `ModernConvex.EllipsoidMethod.EllipsoidMethod`) with accuracy $\epsilon > 0$, an arbitrary separation oracle for $X$ and an arbitrary first order oracle for $f$. Let
--   $$\operatorname{Var}_R(f) = \max_{E_0} f - \min_{E_0} f .$$
--   Then the method terminates after no more than
--   $$N(\epsilon) = \operatorname{Ceil}\Big(2n^2\Big[\ln\Big(\frac Rr\Big) + \ln\Big(\frac{\epsilon + \operatorname{Var}_R(f)}{\epsilon}\Big)\Big]\Big) + 1$$
--   steps, where $\operatorname{Ceil}(a)$ is the smallest integer $\ge a$, and its result $\widehat x$ is a feasible $\epsilon$-solution:
--   $$\widehat x \in X \quad\text{and}\quad f(\widehat x) - \min_X f \le \epsilon.$$
--
--   The step count depends on the data only through $n$, $R/r$ and $\operatorname{Var}_R(f)/\epsilon$, and each step costs one call of each oracle and $O(n^2)$ arithmetic operations; this is the basis of the book's polynomial solvability theorem for convex programs.
--
--   **Formalization Note** The book's (5.2.19) prints $f(x) - \min_X f \le \epsilon$, a typo for $f(\widehat x)$. "Terminates after no more than $N(\epsilon)$ steps" is: there is a step $t \le N(\epsilon)$ (compared in $\mathbb Z$, Ceil being `Int.ceil`) at which the method terminates, with result $\widehat x$. $\min_X f$ is expressed by "$f(\widehat x) - f(y) \le \epsilon$ for all $y \in X$", and $\max_{E_0} f$, $\min_{E_0} f$ by reals `Vmax`, `Vmin` that are the greatest and least elements of $f(E_0)$. The oracles are arbitrary functions of the query point satisfying (5.2.10) and (5.2.11); the method sees $R$, $r$ and $\epsilon$ but not the centre of the ball of radius $r$ inside $X$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 349, Theorem 5.2.1, (5.2.18)–(5.2.19)

import Mathlib
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod

open Matrix MeasureTheory

namespace ModernConvex.EllipsoidMethod

/-- Ben-Tal–Nemirovski, p. 349, Theorem 5.2.1. Let the ellipsoid method be applied to the convex
program (5.2.9) of dimension `n ≥ 2` whose feasible set `X` contains a Euclidean ball of a
given radius `r > 0` and is contained in the ball `E₀ = {‖x‖₂ ≤ R}`, with a separation oracle
for `X` and a first order oracle for `f`. For every accuracy `ε > 0` the method terminates
after no more than `N(ε) = Ceil(2n²[ln(R/r) + ln((ε + Var_R(f))/ε)]) + 1` steps (5.2.18), where
`Var_R(f) = max_{E₀} f − min_{E₀} f`, and its result `x̂` satisfies `x̂ ∈ X` and
`f(x̂) − min_X f ≤ ε` (5.2.19). -/
theorem ellipsoid_method_complexity {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin) :
    ∃ (t : ℕ) (xhat : Fin n → ℝ),
      (t : ℤ) ≤ ⌈2 * (n : ℝ) ^ 2 *
          (Real.log (R / r) + Real.log ((ε + (Vmax - Vmin)) / ε))⌉ + 1 ∧
      TerminatesAt sep O R r ε t (some xhat) ∧
      xhat ∈ X ∧ ∀ y ∈ X, f xhat - f y ≤ ε := by sorry

end ModernConvex.EllipsoidMethod
