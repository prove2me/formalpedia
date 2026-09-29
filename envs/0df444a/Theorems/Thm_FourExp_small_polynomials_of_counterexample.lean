-- Prove2me | Theorems.Thm_FourExp_small_polynomials_of_counterexample
-- name    : FourExp.small_polynomials_of_counterexample
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-14T19:13:11.175868+00:00
-- url     : https://prove2.me/theorems/81f3c358-88a8-46e9-a5af-5c2c359b63f6
-- title:
--   A four-exponentials counterexample in transcendence degree one yields polynomials too small at a transcendental number
-- statement:
--   **The analytic core of the Brownawell–Waldschmidt proof: a counterexample produces polynomials that are too small.**
--
--   Let $l_{11}, l_{12}, l_{21}, l_{22}$ be non-zero complex numbers with $e^{l_{ij}}$ algebraic, $l_{11}l_{22} = l_{12}l_{21}$, and $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}[l_{11}, l_{12}, l_{21}, l_{22}] \le 1$. Suppose that **neither** the two rows **nor** the two columns of $\begin{pmatrix} l_{11} & l_{12} \\ l_{21} & l_{22} \end{pmatrix}$ are linearly dependent over $\mathbb{Q}$.
--
--   Then there is a transcendental $\omega \in \mathbb{C}$, together with growth functions $\sigma_1, \sigma_2$ and constants $a_1, a_2 \ge 1$ satisfying the hypotheses of `FourExp.transcendence_criterion`, such that for **every** $C$ and all large $N$ there is a non-zero $P_N \in \mathbb{Z}[X]$ with
--   $$|\text{coefficients of } P_N| \le e^{\sigma_1(N)}, \qquad \deg P_N \le \sigma_2(N), \qquad |P_N(\omega)| < e^{-C\,\sigma_1(N)\,\sigma_2(N)} .$$
--
--   **What it is for.** Combined with `FourExp.transcendence_criterion` it proves `DiazModulus.four_exponentials_trdeg_one` by contradiction: the criterion makes $\omega$ algebraic. The reduction is submitted against that node.
--
--   **Honesty about its shape.** By the four exponentials theorem in transcendence degree one, the hypotheses here are never satisfied, so this statement follows from its parent. It is **not** a weaker problem. It is the constructive half of a proof by contradiction, and the intended proof builds the polynomials. In Waldschmidt's proof, that means:
--   - write the field as $L(\omega, \omega_1)$ with $\omega$ transcendental;
--   - build an auxiliary function $\sum q(\lambda)\, z^{\lambda_0} e^{(\lambda_1 x_1 + \lambda_2 x_2) z}$ with Siegel's lemma;
--   - extrapolate with the maximum principle;
--   - find a non-zero value using the zero count `FourExp.expPoly_zero_count`;
--   - take norms down to $\mathbb{Q}(\omega)$.
--
--   In that construction $\sigma_1(N) \asymp N^2(\log N)^{1/2}$ and $\sigma_2(N) \asymp N^2(\log N)^{-1/2}$, while $|P_N(\omega)| \le \exp(-\tfrac18 N^4 (\log N)^{1/2})$. That is why every $C$ is eventually beaten.
--
--   **Formalization.** The rank-one parametrisation $l_{ij} = x_i y_j$ (with $x_1, x_2$ and $y_1, y_2$ each $\mathbb{Q}$-independent) is left to the proof, so that the statement uses exactly the hypotheses of the parent node.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, §III, Lemmas 4–7; with the zero estimate of M. Waldschmidt, Bull. Soc. Math. France 99 (1971), 285–304, §4, Lemma 3, in place of the hypotheses (iii)–(iv) of Gel'fond's lemma. See also W. D. Brownawell, J. Number Theory 6 (1974), 22–31.

import Mathlib

open Filter Topology

namespace FourExp

theorem small_polynomials_of_counterexample :
    ∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ,
      IsAlgebraic ℚ (Complex.exp l₁₁) → IsAlgebraic ℚ (Complex.exp l₁₂) →
      IsAlgebraic ℚ (Complex.exp l₂₁) → IsAlgebraic ℚ (Complex.exp l₂₂) →
      l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 →
      l₁₁ * l₂₂ = l₁₂ * l₂₁ →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
      ¬ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0) →
      ¬ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) →
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
