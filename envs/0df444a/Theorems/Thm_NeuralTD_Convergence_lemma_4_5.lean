-- Prove2me | Theorems.Thm_NeuralTD_Convergence_lemma_4_5
-- name    : NeuralTD.Convergence.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:27.334795+00:00
-- url     : https://prove2.me/theorems/4d826b7a-7d0f-44fd-88be-1748f3b17330
-- title:
--   Lemma 4.5, p. 11 — E_init,µ[‖g(t) − ḡ(t)‖²₂] ≤ σ²_g with the explicit σ²_g = 12 + 12B² + 3r̄² of its proof (B.6)–(B.7)
-- statement:
--   Let $\mu$ be a sampling law with reward bound $\bar r \ge 0$, let $0 \le \gamma < 1$, $B \ge 0$ and let $\eta$ be any step size. Run Algorithm 1 from an initialization $(b, W(0))$ drawn from the initialization law, with i.i.d. samples from $\mu$ independent of the initialization. Let $g(t) = \delta(x_t, r_t, x'_t; W(t))\,\nabla_W\widehat Q(x_t; W(t))$ be the stochastic semigradient at step $t$ and $\bar g(t) = \bar g(W(t))$ its conditional mean. Then for every $t$,
--   $$\mathbb E_{\mathrm{init},\mu}\big[\|g(t) - \bar g(t)\|_2^2\big] \le \sigma_g^2, \qquad \sigma_g^2 = 12 + 12B^2 + 3\bar r^2 .$$
--
--   The variance proxy $\sigma_g^2 = O(B^2)$ is what forces the step size $\eta \asymp T^{-1/2}$ in Theorem 4.6 and appears in its leading term.
--
--   **Formalization Note.** The paper states "there exists $\sigma_g^2 = O(B^2)$"; the explicit value used here is the one its proof produces ((B.6) with $\mathbb E_{\mathrm{init},\mu}[\widehat Q_0(x)^2] \le 1$ from (B.7)), and it is the value that enters the goal theorem. The expectation is over the initialization and the run's samples ($\mathbb N$-indexed, product law).
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, p. 11, Lemma 4.5 (proof: Appendix B.2, p. 27)

import Mathlib
import Definitions.Def_NeuralTD_Convergence_Setting

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Lemma 4.5 (p. 11) with the explicit variance proxy `σ_g² = 12 + 12B² + 3r̄²` of its proof
((B.6)–(B.7)): `E_init,μ[‖g(t) − ḡ(t)‖₂²] ≤ σ_g²` for every step `t`. -/
theorem lemma_4_5 (m d : ℕ) (B rbar γ η : ℝ) (hB : 0 ≤ B) (hrbar : 0 ≤ rbar) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (μ : Measure (Sample d)) (hμ : IsSamplingLaw d rbar μ) (t : ℕ) :
    ∫⁻ ι, ∫⁻ ξs, ENNReal.ofReal
        (‖delta γ ι.1 (iterate γ η B ι ξs t) (ξs t) • gradQ ι.1 (iterate γ η B ι ξs t) (ξs t).1
          - gbar γ μ ι.1 (iterate γ η B ι ξs t)‖ ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => μ) ∂(initLaw m d)
      ≤ ENNReal.ofReal (12 + 12 * B ^ 2 + 3 * rbar ^ 2) := by sorry

end NeuralTD.Convergence
