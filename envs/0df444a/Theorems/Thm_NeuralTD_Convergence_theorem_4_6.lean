-- Prove2me | Theorems.Thm_NeuralTD_Convergence_theorem_4_6
-- name    : NeuralTD.Convergence.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:27.862152+00:00
-- url     : https://prove2.me/theorems/b845b9bc-8dff-4efb-bbfe-3d71bb5afb33
-- title:
--   Theorem 4.6, p. 11 — neural TD with stochastic semigradients: E[(Q̂out − Q̂0(·; W*))²] ≤ 16(B² + σ²_g)/((1−γ)²√T) + C(B³m^{−1/2} + B^{5/2}m^{−1/4})
-- statement:
--   Let $d \ge 3$, $c_0 > 0$, $\bar r \ge 0$ and $0 \le \gamma < 1$. There is a constant $C$, depending only on $c_0$, $d$, $\bar r$ and $\gamma$, such that the following holds for every width $m \ge 1$, radius $B \ge 1$ and number of iterations $T \ge 1$.
--
--   Let $\mu$ be a sampling law with reward bound $\bar r$ satisfying Assumption 4.3 with constant $c_0$. Draw $(b, W(0))$ from the initialization law ($b_r \sim \mathrm{Unif}\{-1,1\}$, $W_r(0) \sim N(0, I_d/d)$), run Algorithm 1 for $T$ iterations with step size $\eta = \min\{(1-\gamma)/8, 1/\sqrt T\}$ on i.i.d. samples from $\mu$, and let $\widehat Q_{\mathrm{out}} = \widehat Q(\cdot\,;\overline W)$ be its output. For every choice of approximate stationary point $W^*$ (depending on the initialization),
--   $$\mathbb E_{\mathrm{init},\mu}\Big[\big(\widehat Q_{\mathrm{out}}(x) - \widehat Q_0(x; W^*)\big)^2\Big] \le \frac{16\,(B^2 + \sigma_g^2)}{(1-\gamma)^2\sqrt T} + C\big(B^3 m^{-1/2} + B^{5/2} m^{-1/4}\big), \qquad \sigma_g^2 = 12 + 12B^2 + 3\bar r^2,$$
--   where the expectation is over the initialization, the samples of the run and a fresh $x \sim \mu$.
--
--   Neural TD thus converges at rate $T^{-1/2}$, up to a width-dependent error, to $\widehat Q_0(\cdot\,;W^*)$, which by Lemma 4.2 is the global optimum of the mean-squared projected Bellman error over the class $\mathcal F_{B,m}$.
--
--   **Formalization Note.**
--   1. $\sigma_g^2 = 12 + 12B^2 + 3\bar r^2$ is the explicit value from the proof of Lemma 4.5 ((B.6)–(B.7)); the paper writes "$\sigma_g^2 = O(B^2)$".
--   2. The paper's $O(B^3m^{-1/2} + B^{5/2}m^{-1/4})$ is the constant $C$, quantified before $m$, $B$, $T$, $\mu$ and $W^*$. It depends on $\gamma$ (through $1/(1-\gamma)$ in the proof) and on $\bar r$; the restriction $B \ge 1$ lets the lower-order terms $B$ and $B\bar r^2$ of Lemma 5.2 be absorbed into $B^3$.
--   3. $W^*$ is any selection $\iota \mapsto W^*(\iota)$ of approximate stationary points, one per initialization; by Lemma 4.2 the function $\widehat Q_0(\cdot\,; W^*)$ does not depend on the selection up to $\mu$-null sets. Approximate stationary points lie in $S_B$ by definition.
--   4. The expectation is a lower Lebesgue integral of a nonnegative integrand, so it cannot be made vacuous by non-integrability. $d \ge 3$ is the paper's $d > 2$.
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, p. 11, Theorem 4.6 (proof: Appendix C.6, pp. 35–36)

import Mathlib
import Definitions.Def_NeuralTD_Convergence_Setting

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Theorem 4.6 (p. 11): with `η = min{(1 − γ)/8, 1/√T}` and under Assumption 4.3, the output of
neural TD satisfies `E_init,μ[(Q̂_out(x) − Q̂₀(x; W*))²] ≤ 16(B² + σ_g²)/((1 − γ)²√T)
+ O(B³ m^{−1/2} + B^{5/2} m^{−1/4})`, with `σ_g² = 12 + 12B² + 3r̄²` and the `O(·)` constant
depending only on `c₀, d, r̄, γ`. -/
theorem theorem_4_6 (d : ℕ) (hd : 3 ≤ d) (c0 rbar γ : ℝ) (hc0 : 0 < c0) (hrbar : 0 ≤ rbar)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, ∀ (m : ℕ), 1 ≤ m → ∀ (B : ℝ), 1 ≤ B → ∀ (T : ℕ), 1 ≤ T →
      ∀ μ : Measure (Sample d), IsSamplingLaw d rbar μ → Assumption43 c0 μ →
      ∀ Wst : Init m d → Param m d, (∀ ι, IsApproxStationary γ μ B ι.1 ι.2 (Wst ι)) →
        ∫⁻ ι, ∫⁻ ξs, ∫⁻ ξ, ENNReal.ofReal ((Qout γ B ι ξs T ξ.1 - Qlin ι.1 ι.2 (Wst ι) ξ.1) ^ 2)
            ∂μ ∂(Measure.infinitePi fun _ : ℕ => μ) ∂(initLaw m d)
          ≤ ENNReal.ofReal (16 * (B ^ 2 + (12 + 12 * B ^ 2 + 3 * rbar ^ 2)) /
                ((1 - γ) ^ 2 * Real.sqrt T)
              + C * (B ^ 3 * (m : ℝ) ^ (-(1 / 2 : ℝ)) + B ^ (5 / 2 : ℝ) * (m : ℝ) ^ (-(1 / 4 : ℝ))))
          := by sorry

end NeuralTD.Convergence
