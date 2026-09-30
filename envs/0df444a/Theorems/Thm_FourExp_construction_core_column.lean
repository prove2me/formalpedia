-- Prove2me | Theorems.Thm_FourExp_construction_core_column
-- name    : FourExp.construction_core_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:40:33.527378+00:00
-- url     : https://prove2.me/theorems/690b22eb-5683-42a9-b0ee-fd8096209490
-- title:
--   Non-zero derivatives of the auxiliary function on the 14-fold grid give integer polynomials small at ω, when only e^{x₁y₂} and e^{x₂y₂} are algebraic
-- statement:
--   Let $x_1, x_2$ be $\mathbb{Q}$-linearly independent, and likewise $y_1, y_2$. Suppose that $e^{x_1y_2}$ and $e^{x_2y_2}$ are algebraic and that $\mathbb{Q}[x_1, x_2, y_1, y_2, e^{x_1y_1}, e^{x_2y_1}]$ has transcendence degree at most one. Then there are a transcendental $\omega$ and $k > 0$ such that for every $C$ and every large $N$, with
--
--   $$S = \lfloor N^{2}/\sqrt{\log N}\rfloor,\quad t_1 = \lfloor N/\sqrt{\log N}\rfloor,\quad t_2 = \lfloor N\sqrt{\log N}\rfloor,$$
--
--   there are coefficients $c_{ijk}$, not all zero, with the following property. Put $F(z) = \sum_{i<S}\sum_{j,k<2N} c_{ijk}\, z^{i} e^{(jx_1 + kx_2)z}$. Every non-zero $F^{(s)}(ay_1 + by_2)$ with $a < 14t_1$, $b < 14t_2$ and $s < S/2$ gives a non-zero $P \in \mathbb{Z}[X]$ with coefficients at most $e^{kN^{2}\sqrt{\log N}}$, degree at most $kN^{2}/\sqrt{\log N}$ and $|P(\omega)| < e^{-Ck^{2}N^{4}}$.
--
--   This is `FourExp.construction_core_1973` with only $e^{x_1y_2}$, $e^{x_2y_2}$ assumed algebraic and with $e^{x_1y_1}$, $e^{x_2y_1}$ joining $x_1, x_2, y_1, y_2$ in the transcendence-degree hypothesis; in Waldschmidt (1973) it is Lemmes 4, 5 and 7 together, with $N$, $S$, $t_1$, $t_2$ the paper's $t_0$, $s_0$, $t_1$, $t_2$. The proof chains `FourExp.trdeg_one_presentation_column`, `FourExp.exists_iteratedDeriv_reduced_presentation_column`, `FourExp.auxiliary_function_alg_column`, `FourExp.extrapolation` and `FourExp.norm_to_polynomial_alg_column`; $e^{x_1y_1}$ and $e^{x_2y_1}$ are read only at the short index $a$. The hypotheses never hold together, by `DiazModulus.two_algebraically_independent_of_exp_column`: this node is a step of its proof by contradiction.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemmes 4, 5 and 7, with the parameters of p. 196, where s₀ = [t₀²(log t₀)^(−1/2)] as in the outline on p. 195 (formula (4) prints the exponent +1/2). Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- The core of Waldschmidt's construction of 1973, in the column case.

Let `x₁, x₂` and `y₁, y₂` be `ℚ`-linearly independent, with the column `e^{x₁y₂}`, `e^{x₂y₂}`
algebraic (`hexp₂`), and suppose that `ℚ[x₁, x₂, y₁, y₂, e^{x₁y₁}, e^{x₂y₁}]` has transcendence
degree at most one. Put `s = √(log N)`, `S = ⌊N²/s⌋`, `t₁ = ⌊N/s⌋`, `t₂ = ⌊N s⌋`. Then there are a
transcendental `ω` and `k > 0` such that, for every `C` and every large `N`, some exponential
polynomial `F(z) = ∑_{i<S, j,k<2N} c_{ijk} z^i e^{(j x₁ + k x₂) z}` with a non-zero coefficient has
the following property: every non-zero `F⁽ˢ⁾(a y₁ + b y₂)` with `a < 14 t₁`, `b < 14 t₂`,
`s < S/2` gives an integer polynomial `P ≠ 0` of height at most `e^{k N² s}`, degree at most
`k N²/s`, and `|P(ω)| < e^{-C (k N² s)(k N²/s)}` (the scales are glued below `N = 3` as in
`FourExp.construction_growth`).

This is `FourExp.construction_core_1973` with the column hypothesis in place of the four algebraic
exponentials. The column exponentials sit on the long index `b`; `e^{x₁y₁}` and `e^{x₂y₁}` are only
algebraic over `ℚ(ω)`, and they are read at the short index `a`. -/
theorem construction_core_column
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp₂ : ∀ i : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * y₂)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁),
      Complex.exp (x₂ * y₁)} : Set ℂ)) ≤ 1) :
    ∃ ω : ℂ, Transcendental ℚ ω ∧ ∃ k : ℝ, 0 < k ∧
      ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
        ∃ c : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → ℂ, (∃ i j k', c i j k' ≠ 0) ∧
          ∀ a b s : ℕ, a < (14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊) → b < (14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊) → s < (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2) →
            iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
              ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 →
            ∃ P : Polynomial ℤ, P ≠ 0 ∧
              (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
              (P.natDegree : ℝ) ≤ k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) ∧
              ‖Polynomial.aeval ω P‖ < Real.exp (-(C * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)))))) := by
  sorry

end FourExp
