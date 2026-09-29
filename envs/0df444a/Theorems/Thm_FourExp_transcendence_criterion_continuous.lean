-- Prove2me | Theorems.Thm_FourExp_transcendence_criterion_continuous
-- name    : FourExp.transcendence_criterion_continuous
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T04:28:46.115078+00:00
-- url     : https://prove2.me/theorems/edd2f289-6d1c-476d-ad9a-5b7015839de3
-- title:
--   Gel'fond-type transcendence criterion with continuous growth functions
-- statement:
--   **The transcendence criterion, for continuous growth functions.**
--
--   This is `FourExp.transcendence_criterion` with two changes. The functions $\sigma_1, \sigma_2$ are also assumed **continuous**. The conditions
--   $$\sigma_2(x) \le \sigma_1(x), \qquad \sigma_i(x+1) \le a_i\,\sigma_i(x)$$
--   are required only for $x \ge 1$, not for $x > 0$.
--
--   Explicitly: let $\alpha \in \mathbb{C}$ and $\varepsilon > 0$. Let $\sigma_1, \sigma_2$ be continuous, strictly increasing and unbounded, and let $a_1, a_2 \ge 1$ satisfy the conditions above for $x \ge 1$. Suppose that for all $N > N_0$ there is a non-zero $P_N \in \mathbb{Z}[X]$ with coefficients at most $e^{\sigma_1(N)}$, degree at most $\sigma_2(N)$, and $|P_N(\alpha)| < \exp(-C\sigma_1(N)\sigma_2(N))$, where $C = \max\{10+\varepsilon, (4+\varepsilon)a_1a_2\}$. Then $\alpha$ is algebraic.
--
--   **Why this form.** Waldschmidt's proof (1971, §3) inverts $\sigma_i$: it defines $z_q = \max\bigl(\sigma_1^{-1}(\tfrac13\log h_q),\ \sigma_2^{-1}((1+\tfrac\varepsilon2)^{-1}\delta_q)\bigr)$ and uses $\sigma_i(\sigma_i^{-1}(y)) = y$, which needs continuity. The paper notes that continuity can be assumed, since only integer values matter. That step is the accepted reduction from `FourExp.transcendence_criterion`, by piecewise-linear interpolation. The proof only ever uses large $x$, so asking the conditions for $x \ge 1$ loses nothing, and interpolation cannot preserve them on $(0, 1)$ in general.
--
--   **Intended proof.** The 1971 argument, using Gel'fond's height inequality for a divisor, Gel'fond's small-irreducible-factor lemma, and the resultant bound that forces $Q_q \mid P_N$.
-- source:
--   M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §3, Lemme fondamental and its proof (continuity of σᵢ is assumed there without loss of generality).

import Mathlib

open Filter Topology

namespace FourExp

theorem transcendence_criterion_continuous
    (α : ℂ) (ε : ℝ) (hε : 0 < ε)
    (σ₁ σ₂ : ℝ → ℝ) (hσ₁ : StrictMono σ₁) (hσ₂ : StrictMono σ₂)
    (hσ₁c : Continuous σ₁) (hσ₂c : Continuous σ₂)
    (hσ₁t : Tendsto σ₁ atTop atTop) (hσ₂t : Tendsto σ₂ atTop atTop)
    (a₁ a₂ : ℝ) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (h₂₁ : ∀ x : ℝ, 1 ≤ x → σ₂ x ≤ σ₁ x)
    (hgrowth₁ : ∀ x : ℝ, 1 ≤ x → σ₁ (x + 1) ≤ a₁ * σ₁ x)
    (hgrowth₂ : ∀ x : ℝ, 1 ≤ x → σ₂ (x + 1) ≤ a₂ * σ₂ x)
    (N₀ : ℕ) (P : ℕ → Polynomial ℤ)
    (hP_ne : ∀ N : ℕ, N₀ < N → P N ≠ 0)
    (hP_height : ∀ N : ℕ, N₀ < N → ∀ i : ℕ, |((P N).coeff i : ℝ)| ≤ Real.exp (σ₁ N))
    (hP_deg : ∀ N : ℕ, N₀ < N → ((P N).natDegree : ℝ) ≤ σ₂ N)
    (hP_small : ∀ N : ℕ, N₀ < N →
      ‖Polynomial.aeval α (P N)‖ <
        Real.exp (-(max (10 + ε) ((4 + ε) * (a₁ * a₂)) * σ₁ N * σ₂ N))) :
    IsAlgebraic ℚ α := by
  sorry

end FourExp
