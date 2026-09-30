-- Prove2me | Theorems.Thm_FourExp_small_polynomials_of_column
-- name    : FourExp.small_polynomials_of_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:40:19.971644+00:00
-- url     : https://prove2.me/theorems/4b4429d8-3091-408a-8b30-d661d6c0a9ef
-- title:
--   When only e^{x₁y₂} and e^{x₂y₂} are algebraic, transcendence degree one yields integer polynomials too small at a transcendental number
-- statement:
--   Let $x_1, x_2$ be $\mathbb{Q}$-linearly independent, and likewise $y_1, y_2$. Suppose that $e^{x_1y_2}$ and $e^{x_2y_2}$ are algebraic and that
--
--   $$\operatorname{trdeg}_{\mathbb{Q}}\, \mathbb{Q}[x_1, x_2, y_1, y_2, e^{x_1y_1}, e^{x_2y_1}] \le 1.$$
--
--   Then there are a transcendental $\omega$ and growth functions $\sigma_1, \sigma_2$ with constants $a_1, a_2 \ge 1$, satisfying the hypotheses of `FourExp.transcendence_criterion`, such that for every $C$ there are non-zero $P_N \in \mathbb{Z}[X]$ for all large $N$, with coefficients at most $e^{\sigma_1(N)}$, degree at most $\sigma_2(N)$ and
--
--   $$|P_N(\omega)| < e^{-C\sigma_1(N)\sigma_2(N)}.$$
--
--   This is `FourExp.small_polynomials_of_counterexample` with only $e^{x_1y_2}$ and $e^{x_2y_2}$ assumed algebraic and with $e^{x_1y_1}$, $e^{x_2y_1}$ in the transcendence-degree hypothesis, stated for given $x$ and $y$ instead of a $2 \times 2$ matrix of logarithms. In Waldschmidt (1973) it is Lemmes 4–7 together: `FourExp.auxiliary_construction_column` builds the auxiliary function, and `FourExp.nonvanishing_derivative` finds a non-zero derivative on the grid. Gel'fond's criterion then makes $\omega$ algebraic, which is the contradiction in `DiazModulus.two_algebraically_independent_of_exp_column`; so the hypotheses never hold together.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemmes 4–7, with the zero estimate of M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, Lemme 3, in place of Gel'fond's zero lemma (Lemme 2 of the 1973 paper) in Lemme 6. Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

open Filter Topology

namespace FourExp

/-- The analytic half of Waldschmidt's theorem of 1973, in the column case.

Let `x₁, x₂` and `y₁, y₂` be `ℚ`-linearly independent, with `e^{x₁y₂}` and `e^{x₂y₂}` algebraic,
and suppose that `ℚ[x₁, x₂, y₁, y₂, e^{x₁y₁}, e^{x₂y₁}]` has transcendence degree at most one.
Then there are a transcendental `ω` and integer polynomials `P_N ≠ 0`, of height at most
`e^{σ₁(N)}` and degree at most `σ₂(N)`, with `|P_N(ω)| < e^{-C σ₁(N) σ₂(N)}` for every `C`; the
functions `σ₁, σ₂` satisfy the growth conditions of Gel'fond's criterion
(`FourExp.transcendence_criterion`), which then makes `ω` algebraic.

This is `FourExp.small_polynomials_of_counterexample` with the column hypothesis in place of the
four algebraic exponentials. -/
theorem small_polynomials_of_column :
    ∀ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₂)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂)) →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁),
          Complex.exp (x₂ * y₁)} : Set ℂ)) ≤ 1 →
      ∃ ω : ℂ, Transcendental ℚ ω ∧
        ∃ σ₁ σ₂ : ℝ → ℝ, StrictMono σ₁ ∧ StrictMono σ₂ ∧
          Tendsto σ₁ atTop atTop ∧ Tendsto σ₂ atTop atTop ∧
          ∃ a₁ a₂ : ℝ, 1 ≤ a₁ ∧ 1 ≤ a₂ ∧
            (∀ x : ℝ, 0 < x → σ₂ x ≤ σ₁ x) ∧
            (∀ x : ℝ, 0 < x → σ₁ (x + 1) ≤ a₁ * σ₁ x) ∧
            (∀ x : ℝ, 0 < x → σ₂ (x + 1) ≤ a₂ * σ₂ x) ∧
            ∀ C : ℝ, ∃ N₀ : ℕ, ∃ P : ℕ → Polynomial ℤ, ∀ N : ℕ, N₀ < N →
              P N ≠ 0 ∧
              (∀ i : ℕ, |((P N).coeff i : ℝ)| ≤ Real.exp (σ₁ N)) ∧
              ((P N).natDegree : ℝ) ≤ σ₂ N ∧
              ‖Polynomial.aeval ω (P N)‖ < Real.exp (-(C * σ₁ N * σ₂ N)) := by
  sorry

end FourExp
