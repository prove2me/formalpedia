-- Prove2me | Theorems.Thm_NeuralTD_Convergence_lemma_5_4
-- name    : NeuralTD.Convergence.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:21.086057+00:00
-- url     : https://prove2.me/theorems/05dab571-7293-4bb1-8d66-981eee37f713
-- title:
--   Lemma 5.4, p. 14 — stochastic descent lemma for neural TD, with the printed 2ηB corrected to 4ηB (‖W(t) − W*‖₂ ≤ 2B)
-- statement:
--   Let $\mu$ be a sampling law, $0 \le \gamma < 1$, $B \ge 0$, $\eta > 0$. Fix an initialization $(b, W(0))$ with $b \in \{-1,1\}^m$ and an approximate stationary point $W^*$. Run Algorithm 1 with step size $\eta$ on i.i.d. samples from $\mu$, and write $\mathbb E_W$ for the expectation over the samples. Then for every $t$,
--   $$\begin{aligned}\mathbb E_{W}\big[\|W(t+1) - W^*\|_2^2\big] \le{}& \mathbb E_W\big[\|W(t) - W^*\|_2^2\big] - \big(2\eta(1-\gamma) - 8\eta^2\big)\,\mathbb E_{W,\mu}\Big[\big(\widehat Q_0(x;W(t)) - \widehat Q_0(x;W^*)\big)^2\Big] \\ &+ \mathbb E_W\Big[2\eta^2\|\bar g(t) - \bar g_0(t)\|_2^2 + 4\eta B\,\|\bar g(t) - \bar g_0(t)\|_2\Big] + \mathbb E_{W}\big[\eta^2\|g(t) - \bar g(t)\|_2^2\big],\end{aligned}$$
--   where $g(t)$ is the stochastic semigradient at the sample of step $t$, $\bar g(t) = \bar g(W(t))$, $\bar g_0(t) = \bar g_0(W(t))$, and $x \sim \mu$ is a fresh draw.
--
--   The distance to $W^*$ decreases by a multiple of the squared $\mu$-error of the linearized Q-function, up to a linearization error and a variance term; telescoping this over $t$ gives Theorem 4.6.
--
--   **Formalization Note.** The page prints the coefficient $2\eta B$ in front of $\|\bar g(t) - \bar g_0(t)\|_2$. Its proof bounds $(\bar g(t) - \bar g_0(t))^\top(W(t) - W^*)$ by Cauchy–Schwarz, and both $W(t)$ and $W^*$ lie in $S_B$, so $\|W(t) - W^*\|_2 \le 2B$ and the argument establishes $4\eta B$; the statement uses $4\eta B$. The lemma is stated for one fixed initialization with $b \in \{\pm1\}^m$ (which the initialization law gives almost surely, and which yields $\|\nabla_W\widehat Q_0\|_2 \le 1$). The expectations are Bochner integrals of functions that are bounded for fixed initialization (since $\|x\|_2 = 1$ and $|r| \le \bar r$ almost surely and all iterates lie in $S_B$), hence integrable.
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, p. 14, Lemma 5.4 (proof: Appendix C.4, pp. 33–34)

import Mathlib
import Definitions.Def_NeuralTD_Convergence_Setting

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Lemma 5.4 (p. 14), stochastic descent lemma, for a fixed initialization with `b ∈ {±1}^m`;
the expectation `E_W` is over the samples of the run. The coefficient of
`‖ḡ(t) − ḡ₀(t)‖₂` is `4ηB` (the page prints `2ηB`; its proof bounds `‖W(t) − W*‖₂ ≤ 2B`). -/
theorem lemma_5_4 {m d : ℕ} (γ rbar B η : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hB : 0 ≤ B)
    (hη : 0 < η) (μ : Measure (Sample d)) (hμ : IsSamplingLaw d rbar μ) (ι : Init m d)
    (hb : ∀ r, ι.1 r = 1 ∨ ι.1 r = -1) (Wst : Param m d)
    (hst : IsApproxStationary γ μ B ι.1 ι.2 Wst) (t : ℕ) :
    ∫ ξs, ‖iterate γ η B ι ξs (t + 1) - Wst‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ∫ ξs, ‖iterate γ η B ι ξs t - Wst‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => μ)
      - (2 * η * (1 - γ) - 8 * η ^ 2) *
          ∫ ξs, ∫ ξ, (Qlin ι.1 ι.2 (iterate γ η B ι ξs t) ξ.1 - Qlin ι.1 ι.2 Wst ξ.1) ^ 2 ∂μ
            ∂(Measure.infinitePi fun _ : ℕ => μ)
      + ∫ ξs, (2 * η ^ 2 * ‖gbar γ μ ι.1 (iterate γ η B ι ξs t)
                - gbarLin γ μ ι.1 ι.2 (iterate γ η B ι ξs t)‖ ^ 2
              + 4 * η * B * ‖gbar γ μ ι.1 (iterate γ η B ι ξs t)
                - gbarLin γ μ ι.1 ι.2 (iterate γ η B ι ξs t)‖)
          ∂(Measure.infinitePi fun _ : ℕ => μ)
      + ∫ ξs, η ^ 2 * ‖delta γ ι.1 (iterate γ η B ι ξs t) (ξs t) •
              gradQ ι.1 (iterate γ η B ι ξs t) (ξs t).1
            - gbar γ μ ι.1 (iterate γ η B ι ξs t)‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => μ) := by sorry

end NeuralTD.Convergence
