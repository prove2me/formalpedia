-- Prove2me | Theorems.Thm_FourExp_auxiliary_construction_column
-- name    : FourExp.auxiliary_construction_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:40:22.711448+00:00
-- url     : https://prove2.me/theorems/746d9340-01c6-4aa8-b08a-1c020dfaed36
-- title:
--   An auxiliary function whose grid exceeds the zero count and whose non-zero derivatives give small integer polynomials, when only e^{x₁y₂} and e^{x₂y₂} are algebraic
-- statement:
--   Let $x_1, x_2$ be $\mathbb{Q}$-linearly independent, and likewise $y_1, y_2$. Suppose that $e^{x_1y_2}$ and $e^{x_2y_2}$ are algebraic and that $\mathbb{Q}[x_1, x_2, y_1, y_2, e^{x_1y_1}, e^{x_2y_1}]$ has transcendence degree at most one. Then there are a transcendental $\omega$ and growth functions $\sigma_1, \sigma_2$ with constants $a_1, a_2 \ge 1$, satisfying the hypotheses of `FourExp.transcendence_criterion`, such that for every $C$ and every large $N$ there are integers $S, T, R_1, R_2, S'$, coefficients $c_{ijk}$ ($i < S$, $j, k < T$), not all zero, and $\lambda > 0$ with two properties. First, with $n = ST^{2}$,
--
--   $$\frac{n}{\lambda} + 2\,\frac{1 + n^{\lambda}}{\lambda\log n}\Big(1 + (R_1|y_1| + R_2|y_2|)\,T(|x_1| + |x_2|)\Big) \le R_1R_2S'.$$
--
--   Second, with $G(z) = \sum_{i,j,k} c_{ijk}\, z^{i} e^{(jx_1 + kx_2)z}$, every non-zero $G^{(s)}(ay_1 + by_2)$ with $a < R_1$, $b < R_2$, $s < S'$ gives a non-zero $P \in \mathbb{Z}[X]$ with coefficients at most $e^{\sigma_1(N)}$, degree at most $\sigma_2(N)$ and $|P(\omega)| < e^{-C\sigma_1(N)\sigma_2(N)}$.
--
--   The first property is the zero-count inequality of `FourExp.nonvanishing_derivative`. This is `FourExp.auxiliary_construction` with only $e^{x_1y_2}$ and $e^{x_2y_2}$ assumed algebraic and with $e^{x_1y_1}$, $e^{x_2y_1}$ in the transcendence-degree hypothesis; it is stated for given $x$ and $y$ instead of a $2 \times 2$ matrix of logarithms, so no rank-one parametrisation is needed. In Waldschmidt (1973) it gathers Lemmes 4, 5 and 7 and the count that Lemme 6 needs; here it combines `FourExp.construction_core_column`, `FourExp.construction_growth` and `FourExp.construction_count_1973`. The hypotheses never hold together, by `DiazModulus.two_algebraically_independent_of_exp_column`: this node is a step of its proof by contradiction.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemmes 4, 5 and 7, with the growth functions of p. 201; the count is made for the zero estimate of M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, Lemme 3, which replaces Gel'fond's zero lemma (Lemme 2 of the 1973 paper) in Lemme 6. Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

open Filter Topology

namespace FourExp

/-- The auxiliary construction of Waldschmidt's theorem of 1973, in the column case.

Let `x₁, x₂` and `y₁, y₂` be `ℚ`-linearly independent, with `e^{x₁y₂}` and `e^{x₂y₂}` algebraic,
and suppose that `ℚ[x₁, x₂, y₁, y₂, e^{x₁y₁}, e^{x₂y₁}]` has transcendence degree at most one.
Then there are a transcendental `ω` and functions `σ₁, σ₂` as in Gel'fond's criterion such that,
for every `C` and every large `N`, some exponential polynomial
`F(z) = ∑ c_{ijk} z^i e^{(j x₁ + k x₂) z}` with a non-zero coefficient satisfies the zero-count
inequality of `FourExp.nonvanishing_derivative` on a grid of points `a y₁ + b y₂`, and every
non-zero derivative `F⁽ˢ⁾(a y₁ + b y₂)` on that grid gives an integer polynomial `P ≠ 0` of height
at most `e^{σ₁(N)}` and degree at most `σ₂(N)` with `|P(ω)| < e^{-C σ₁(N) σ₂(N)}`.

This is `FourExp.auxiliary_construction` with the column hypothesis in place of the four algebraic
exponentials. The numbers `x`, `y` are given, so no rank-one parametrization is needed, and the
construction is stated for them. -/
theorem auxiliary_construction_column :
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
            ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
              ∃ (S T R₁ R₂ S' : ℕ) (c : Fin S → Fin T → Fin T → ℂ), (∃ i j k, c i j k ≠ 0) ∧
              (∃ lam : ℝ, 0 < lam ∧ (((S * T * T : ℕ) : ℝ) / lam
              + 2 * (1 + ((S * T * T : ℕ) : ℝ) ^ lam) / (lam * Real.log ((S * T * T : ℕ) : ℝ))
                * (1 + ((R₁ : ℝ) * ‖y₁‖ + (R₂ : ℝ) * ‖y₂‖) * ((T : ℝ) * (‖x₁‖ + ‖x₂‖)))
            ≤ ((R₁ * R₂ * S' : ℕ) : ℝ))) ∧
              ∀ a b s : ℕ, a < R₁ → b < R₂ → s < S' →
                iteratedDeriv s (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              c i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
                  ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 →
                ∃ P : Polynomial ℤ, P ≠ 0 ∧
                  (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (σ₁ N)) ∧
                  (P.natDegree : ℝ) ≤ σ₂ N ∧
                  ‖Polynomial.aeval ω P‖ < Real.exp (-(C * σ₁ N * σ₂ N)) := by
  sorry

end FourExp
