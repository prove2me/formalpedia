-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalInstab_theorem1_4_small_destabilizing_delays
-- name    : NicaiseDelayWave.InternalInstab.theorem1_4_small_destabilizing_delays
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T22:40:12.793272+00:00
-- url     : https://prove2.me/theorems/f334b7da-9a55-49a4-b7b3-8818f046c34a
-- title:
--   Theorem 1.4 (a ≡ 1) — if μ2 ≥ μ1, arbitrarily small and arbitrarily large delays admit solutions whose standard energy does not tend to 0
-- statement:
--   Let $n \ge 1$ and let $(\Omega, \Gamma_D, \Gamma_N)$ be a bounded $C^2$ domain in $\mathbb R^n$ with boundary split $\partial\Omega = \Gamma_D \cup \Gamma_N$, $\overline{\Gamma_D} \cap \overline{\Gamma_N} = \emptyset$, $\Gamma_D \neq \emptyset$. Let $0 < \mu_1 \le \mu_2$, i.e. assumption (1.8) $\mu_2 < \mu_1$ fails. Consider, for a delay $\tau > 0$, the wave equation with delayed internal damping ($a \equiv 1$)
--   $$\begin{cases} u_{tt}(x,t) - \Delta u(x,t) + \mu_1 u_t(x,t) + \mu_2 u_t(x,t-\tau) = 0 & \text{in } \Omega \times (0,\infty), \\ u(x,t) = 0 & \text{on } \Gamma_D \times (0,\infty), \\ \dfrac{\partial u}{\partial\nu}(x,t) = 0 & \text{on } \Gamma_N \times (0,\infty), \end{cases}$$
--   and its standard energy $\mathcal E(t) = \frac12\int_\Omega \{|u_t|^2 + |\nabla u|^2\}\,dx$. Then:
--
--   1. for every $\varepsilon > 0$ there is a delay $\tau \in (0, \varepsilon)$ and a classical solution $u$ with $\mathcal E(t) \not\to 0$ as $t \to \infty$;
--   2. for every $M \in \mathbb R$ there is a delay $\tau > \max(M, 0)$ and a classical solution $u$ with $\mathcal E(t) \not\to 0$ as $t \to \infty$.
--
--   In words: when the delayed feedback is at least as strong as the instantaneous one, arbitrarily small (and arbitrarily large) delays destroy the asymptotic stability that the undelayed damped wave equation enjoys.
--
--   **Formalization Note** Theorem 1.4 is printed for a general damping coefficient $a \in L^\infty(\Omega)$ satisfying (1.17)–(1.18), but §5.2 proves it only for $a \equiv 1$ ("We restrict our analysis to the case $a(x) \equiv 1$ in $\Omega$"); the statement is that case, which is an instance of the paper's problem with $\omega = \Omega$. Solutions are complex valued (the paper's examples are $e^{\lambda t}\varphi(x)$, $\lambda \in \mathbb C$), $C^2$ on $\Omega \times \mathbb R$ and $C^1$ on $\overline\Omega \times \mathbb R$; the initial data (1.15) and history (1.16) are the traces of $u$ at $t = 0$ and on $(-\tau, 0)$. The paper's "sequence of arbitrary small (or large) delays" is stated as the two density properties above. The standing hypotheses (1.6)–(1.7) and the constant $\xi$ of (1.10) play no role here and are omitted. A solution whose energy does not tend to $0$ is in particular nonzero.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1563, Theorem 1.4; proof in §5.2, pp. 1583–1585 (case a ≡ 1)

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalInstab_DelayProblem

namespace NicaiseDelayWave.InternalInstab

open Filter Topology

/-- Nicaise–Pignotti, Theorem 1.4 (p. 1563), for `a ≡ 1` (the case §5.2 proves): if (1.8)
fails, i.e. `μ₁ ≤ μ₂`, there are arbitrarily small and arbitrarily large delays `τ > 0` for which
problem (1.12)–(1.14) (with `a ≡ 1`) has a solution whose standard energy does not tend to `0`. -/
theorem theorem1_4_small_destabilizing_delays {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (μ₁ μ₂ : ℝ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (hμ : μ₁ ≤ μ₂) :
    (∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, 0 < τ ∧ τ < ε ∧
      ∃ u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ, IsClassicalSolution D μ₁ μ₂ τ u ∧
        ¬ Tendsto (stdEnergy D u) atTop (𝓝 0)) ∧
    (∀ M : ℝ, ∃ τ : ℝ, M < τ ∧ 0 < τ ∧
      ∃ u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ, IsClassicalSolution D μ₁ μ₂ τ u ∧
        ¬ Tendsto (stdEnergy D u) atTop (𝓝 0)) := by sorry

end NicaiseDelayWave.InternalInstab
