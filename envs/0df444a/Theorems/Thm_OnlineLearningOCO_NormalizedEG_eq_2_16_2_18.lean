-- Prove2me | Theorems.Thm_OnlineLearningOCO_NormalizedEG_eq_2_16_2_18
-- name    : OnlineLearningOCO.NormalizedEG.eq_2_16_2_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:00.383989+00:00
-- url     : https://prove2.me/theorems/e598a341-167b-44e2-875f-187afa37b49a
-- title:
--   (2.16)–(2.18) — the Bregman term of the log-sum-exp conjugate along normalized EG
-- statement:
--   Let $d \ge 1$, $\eta > 0$, and let $z_1, z_2, \dots \in \mathbb R^d$ be loss vectors. Let $w_t$ be the normalized-EG weights,
--   $$w_t[i] = \frac{e^{-\eta z_{1:t-1}[i]}}{\sum_j e^{-\eta z_{1:t-1}[j]}},$$
--   and let $R^\star(\theta) = \frac1\eta \log\big(\sum_i e^{\eta\theta[i]}\big)$. Then:
--
--   1. $R^\star$ is differentiable on $\mathbb R^d$ with gradient $\nabla R^\star(\theta)[i] = e^{\eta\theta[i]} / \sum_j e^{\eta\theta[j]}$;
--   2. $w_t = \nabla R^\star(-z_{1:t-1})$;
--   3. for every round $t$,
--   $$\begin{aligned} D_{R^\star}(-z_{1:t}\,\|\,-z_{1:t-1}) &= R^\star(-z_{1:t}) - R^\star(-z_{1:t-1}) + \langle w_t, z_t\rangle && (2.16)\\ &= \frac1\eta \log\left(\frac{\sum_i e^{-\eta z_{1:t}[i]}}{\sum_i e^{-\eta z_{1:t-1}[i]}}\right) + \langle w_t, z_t\rangle && (2.17)\\ &= \frac1\eta \log\Big(\sum_i w_t[i]\, e^{-\eta z_t[i]}\Big) + \langle w_t, z_t\rangle. && (2.18)\end{aligned}$$
--
--   These identities turn the Bregman term of Lemma 2.20, for the entropic regularizer, into the logarithm of a weighted average of exponentials, which is then bounded in the next step of the proof of Theorem 2.22.
--
--   **Formalization Note** Rounds are numbered from $0$: `wmWeights η z t` (the published normalized-EG / weighted-majority weights) is the paper's $w_{t+1}$, and `cumSum z t` $= \sum_{s<t} z_s$ is the paper's $z_{1:t}$ for the paper's 1-based indexing of $z$. The gradient is stated as a Fréchet derivative, the linear map $v \mapsto \sum_i \nabla R^\star(\theta)[i]\, v[i]$, because `Fin d → ℝ` is not an inner product space in Mathlib. No restriction on the sign of $z_t$ is needed.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 153, §2.8, proof of Theorem 2.22, (2.16)–(2.18)

import Mathlib
import Definitions.Def_OnlineLearningOCO_NormalizedEG_Duality
import Definitions.Def_UnderstandingML_Online

namespace OnlineLearningOCO.NormalizedEG

open UnderstandingML

/-- §2.8, proof of Theorem 2.22, (2.16)–(2.18), p. 153. For `R⋆(θ) = (1/η) log ∑_i e^{η θ[i]}`
(the conjugate of the normalized entropy, Table 2.1): `R⋆` is differentiable with gradient the
softmax `softmaxEG η`; the normalized-EG weights are `w_t = ∇R⋆(−z_{1:t−1})`; and the Bregman
divergence of `R⋆` along the normalized-EG run satisfies
`D_{R⋆}(−z_{1:t} ‖ −z_{1:t−1}) = R⋆(−z_{1:t}) − R⋆(−z_{1:t−1}) + ⟨w_t, z_t⟩`   (2.16)
`= (1/η) log (∑_i e^{−η z_{1:t}[i]} / ∑_i e^{−η z_{1:t−1}[i]}) + ⟨w_t, z_t⟩`   (2.17)
`= (1/η) log (∑_i w_t[i] e^{−η z_t[i]}) + ⟨w_t, z_t⟩`.   (2.18)
Rounds are 0-based: `wmWeights η z t` is the paper's `w_{t+1}` and `cumSum z t = z_{1:t}` in
the paper's 1-based indexing of `z`. -/
theorem eq_2_16_2_18 {d : ℕ} (hd : 0 < d) (η : ℝ) (hη : 0 < η) (z : ℕ → Fin d → ℝ) (t : ℕ) :
    (∀ θ : Fin d → ℝ, HasFDerivAt (logSumExpConj η)
        (∑ i, softmaxEG η θ i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i) θ) ∧
    softmaxEG η (-(cumSum z t)) = wmWeights η z t ∧
    bregmanLSE η (-(cumSum z (t + 1))) (-(cumSum z t)) =
      logSumExpConj η (-(cumSum z (t + 1))) - logSumExpConj η (-(cumSum z t)) +
        ∑ i, wmWeights η z t i * z t i ∧
    logSumExpConj η (-(cumSum z (t + 1))) - logSumExpConj η (-(cumSum z t)) +
        ∑ i, wmWeights η z t i * z t i =
      (1 / η) * Real.log ((∑ i, Real.exp (-η * cumSum z (t + 1) i)) /
          ∑ i, Real.exp (-η * cumSum z t i)) +
        ∑ i, wmWeights η z t i * z t i ∧
    (1 / η) * Real.log ((∑ i, Real.exp (-η * cumSum z (t + 1) i)) /
          ∑ i, Real.exp (-η * cumSum z t i)) +
        ∑ i, wmWeights η z t i * z t i =
      (1 / η) * Real.log (∑ i, wmWeights η z t i * Real.exp (-η * z t i)) +
        ∑ i, wmWeights η z t i * z t i := by sorry

end OnlineLearningOCO.NormalizedEG
