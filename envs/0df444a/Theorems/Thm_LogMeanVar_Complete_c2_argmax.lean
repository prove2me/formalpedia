-- Prove2me | Theorems.Thm_LogMeanVar_Complete_c2_argmax
-- name    : LogMeanVar.Complete.c2_argmax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:47.293151+00:00
-- url     : https://prove2.me/theorems/30e4e1c3-fab4-4220-bd18-4c3828243e25
-- title:
--   Proof of Theorem 2 (App. C.2), p. O–11 — π̂ = argmax_{v∈ℝ} {v(µ−r) − (1+γ)/2 v²σ²}
-- statement:
--   Let $\mu,r\in\mathbb R$, $\sigma>0$ and $\gamma>0$, and put $\hat\pi=(\mu-r)/((1+\gamma)\sigma^2)$. Then $\hat\pi$ is the unique maximizer over $v\in\mathbb R$ of
--   $$v\mapsto v(\mu-r)-\frac{1+\gamma}2\,v^2\sigma^2 :$$
--   it attains the supremum, and any $v$ attaining the same value equals $\hat\pi$.
--
--   This is the pointwise optimization that turns the spike decomposition into the equilibrium property.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. O-11, Proof of Theorem 2 (App. C.2), last paragraph

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn
import Definitions.Def_LogMeanVar_Complete_Equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LogMeanVar.Complete

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. O–11, Proof of Theorem 2 (App. C.2), last paragraph, first clause:
`π̂ = argmax_{v∈ℝ} {v(μ - r) - (1+γ)/2 v²σ²}`, i.e. `π̂ = (μ - r)/((1 + γ)σ²)` maximizes the
quadratic over `ℝ` and is its only maximizer. -/
theorem c2_argmax (M : Market) (hM : M.Standing) :
    IsMaxOn (fun v : ℝ => v * (M.μ - M.r) - (1 + M.γ) / 2 * v ^ 2 * M.σ ^ 2) Set.univ
        (piHat M) ∧
      ∀ v : ℝ, (v * (M.μ - M.r) - (1 + M.γ) / 2 * v ^ 2 * M.σ ^ 2 =
          piHat M * (M.μ - M.r) - (1 + M.γ) / 2 * piHat M ^ 2 * M.σ ^ 2) → v = piHat M := by sorry

end LogMeanVar.Complete
