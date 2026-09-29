-- Prove2me | Theorems.Thm_FourExp_auxiliary_construction
-- name    : FourExp.auxiliary_construction
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-14T19:24:49.658521+00:00
-- url     : https://prove2.me/theorems/98a064ef-3a62-440c-94b0-56817780aca6
-- title:
--   Waldschmidt's auxiliary function for four exponentials in transcendence degree one
-- statement:
--   **The constructive part of Waldschmidt's 1973 proof: auxiliary function, extrapolation, norms.**
--
--   Assume the hypotheses of `FourExp.small_polynomials_of_counterexample`: a rank-one $2 \times 2$ matrix $(l_{ij})$ of non-zero logarithms of algebraic numbers, whose entries span a ring of transcendence degree at most one, with neither rows nor columns $\mathbb{Q}$-dependent. The node then provides:
--   - a transcendental $\omega$, with growth data $\sigma_1, \sigma_2, a_1, a_2$ satisfying the hypotheses of `FourExp.transcendence_criterion`;
--   - $\mathbb{Q}$-independent pairs $x_1, x_2$ and $y_1, y_2$;
--   - for every $C$ and every large $N$: integers $S, T, R_1, R_2, S'$, not-all-zero coefficients $c(i,j,k)$ defining $G(z) = \sum c(i,j,k)\, z^i e^{(jx_1 + kx_2)z}$, and a $\lambda > 0$, such that
--     - the zero-count inequality of `FourExp.nonvanishing_derivative` holds;
--     - **any** non-zero value $G^{(s)}(a y_1 + b y_2)$ with $a < R_1$, $b < R_2$, $s < S'$ yields a non-zero $P \in \mathbb{Z}[X]$ with coefficients at most $e^{\sigma_1(N)}$, degree at most $\sigma_2(N)$, and $|P(\omega)| < e^{-C\sigma_1(N)\sigma_2(N)}$.
--
--   **Intended proof** (Waldschmidt 1973, §III). The pairs come from writing $l_{ij} = x_i y_j$. The field is written as $L(\omega, \omega_1)$ with $\omega$ transcendental and $\omega_1$ integral over $\mathbb{Z}[\omega]$. Take $t_0 = N$, $s_0 = [t_0^2(\log t_0)^{1/2}]$, $t_1 = [t_0(\log t_0)^{-1/2}]$, $t_2 = [t_0(\log t_0)^{1/2}]$, and $S = s_0$, $T = 2t_0$, $R_1 = 14t_1$, $R_2 = 14t_2$, $S' = [s_0/2]$, $\lambda = 1/20$.
--   - **Lemma 4.** Siegel's lemma gives $G$ vanishing to order $s_0$ on $\{a y_1 + b y_2 : a < t_1,\ b < t_2\}$.
--   - **Lemma 5.** The maximum principle gives $|G^{(s)}(t)| < \exp(-\tfrac12 t_0^4 (\log t_0)^{1/2})$ for $|t| \le t_0 \log t_0$.
--   - **Lemma 7.** The norm from $K$ to $\mathbb{Q}(\omega)$ turns a non-zero value into $P$, with $\deg P \ll t_0^2(\log t_0)^{-1/2}$, $\log H(P) \ll t_0^2(\log t_0)^{1/2}$ and $|P(\omega)| \le \exp(-\tfrac14 t_0^4(\log t_0)^{1/2})$. This beats every $C$.
--
--   The zero-count inequality compares about $80\, t_0^4 (\log t_0)^{1/2}$ with $98\, t_0^4 (\log t_0)^{1/2}$.
--
--   **Honesty about its shape.** As with its parent, the hypotheses are never satisfied (by the four exponentials theorem in transcendence degree one). The node records the constructive half, and is meant to be proved by the construction above.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, §III: formula (4) and Lemmas 4, 5, 7.

import Mathlib

open Filter Topology

namespace FourExp

theorem auxiliary_construction :
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
          ∃ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] ∧ LinearIndependent ℚ ![y₁, y₂] ∧
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
