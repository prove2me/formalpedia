-- Prove2me | Theorems.Thm_NeuralTD_Convergence_lemma_4_2
-- name    : NeuralTD.Convergence.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:16.463468+00:00
-- url     : https://prove2.me/theorems/8cd20fdc-556e-4ae9-beab-17c2594e9e3a
-- title:
--   Lemma 4.2, p. 9 — approximate stationary points exist, Q̂0(·; W*) is unique µ-a.e. and is the MSPBE optimum for the projection onto F_{B,m}
-- statement:
--   Let $\mu$ be a sampling law, $0 \le \gamma < 1$, $B \ge 0$, and fix any output weights $b \in \mathbb R^m$ and any initial parameter $W(0) \in \mathbb R^{md}$. Write $\widehat Q_0(x;W)$ for the local linearization at $W(0)$ and $S_B$ for the ball of radius $B$ around $W(0)$. Then:
--
--   1. **Existence.** There is an approximate stationary point $W^* \in S_B$, i.e. $\bar g_0(W^*)^\top (W - W^*) \ge 0$ for every $W \in S_B$.
--   2. **Uniqueness almost everywhere.** If $W_1^*$ and $W_2^*$ are approximate stationary points, then $\widehat Q_0(x; W_1^*) = \widehat Q_0(x; W_2^*)$ for $\mu$-almost every $x$.
--   3. **Optimality.** Every approximate stationary point $W^*$ minimizes, over $W \in S_B$,
--   $$W \longmapsto \mathbb E_\mu\Big[\big(\widehat Q_0(x;W) - r - \gamma\,\widehat Q_0(x';W^*)\big)^2\Big].$$
--
--   Since $\mathbb E_\mu[(f(x) - r - \gamma Q(x'))^2]$ differs from $\|f - \mathcal T^\pi Q\|_\mu^2$ by a constant independent of $f$, item 3 says that $\widehat Q_0(\cdot\,;W^*)$ is the $\mu$-projection of $\mathcal T^\pi \widehat Q_0(\cdot\,;W^*)$ onto $\mathcal F_{B,m} = \{\widehat Q_0(\cdot\,;W) : W \in S_B\}$: it solves the projected Bellman equation, the global optimum of the mean-squared projected Bellman error. Item 1 shows that the hypothesis on $W^*$ in the convergence theorems can be met for every initialization.
--
--   **Formalization Note.** The Bellman operator $\mathcal T^\pi$ is a conditional expectation of the MDP, which the mission does not model; item 3 states the projection property in the conditional-expectation-free form above. The paper says "for any $b \in \mathbb R^m$", so no $\pm1$ condition is placed on $b$.
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, p. 9, Lemma 4.2 (proof: Appendix B.1, p. 26)

import Mathlib
import Definitions.Def_NeuralTD_Convergence_Setting

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Lemma 4.2 (p. 9): existence, almost-everywhere uniqueness and optimality of `Q̂₀(·; W*)`.
(a) an approximate stationary point exists; (b) `Q̂₀(·; W*)` is unique `μ`-a.e.; (c) `W*`
minimizes `W ↦ E_μ[(Q̂₀(x; W) − r − γ Q̂₀(x′; W*))²]` over `S_B`, i.e. `Q̂₀(·; W*)` is the
projection of `T^π Q̂₀(·; W*)` onto `F_{B,m}` (the MSPBE optimum). -/
theorem lemma_4_2 {m d : ℕ} (γ rbar B : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hB : 0 ≤ B)
    (μ : Measure (Sample d)) (hμ : IsSamplingLaw d rbar μ) (b : Fin m → ℝ) (W0 : Param m d) :
    (∃ Wst : Param m d, IsApproxStationary γ μ B b W0 Wst) ∧
    (∀ W₁ W₂ : Param m d, IsApproxStationary γ μ B b W0 W₁ → IsApproxStationary γ μ B b W0 W₂ →
      ∀ᵐ ξ ∂μ, Qlin b W0 W₁ ξ.1 = Qlin b W0 W₂ ξ.1) ∧
    (∀ Wst : Param m d, IsApproxStationary γ μ B b W0 Wst → ∀ W : Param m d, ‖W - W0‖ ≤ B →
      ∫ ξ, (Qlin b W0 Wst ξ.1 - ξ.2.1 - γ * Qlin b W0 Wst ξ.2.2) ^ 2 ∂μ ≤
        ∫ ξ, (Qlin b W0 W ξ.1 - ξ.2.1 - γ * Qlin b W0 Wst ξ.2.2) ^ 2 ∂μ) := by sorry

end NeuralTD.Convergence
