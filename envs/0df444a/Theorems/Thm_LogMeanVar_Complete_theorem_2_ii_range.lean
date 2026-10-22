-- Prove2me | Theorems.Thm_LogMeanVar_Complete_theorem_2_ii_range
-- name    : LogMeanVar.Complete.theorem_2_ii_range
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:57.605644+00:00
-- url     : https://prove2.me/theorems/34fa8fa3-55b7-4d75-8ddb-abbd1aef5fc1
-- title:
--   Theorem 2(ii), p. 12 — â ∈ (r, r + θ²/2), for µ ≠ r
-- statement:
--   Let $\sigma>0$, $\gamma>0$ and $\mu\neq r$, and put $\theta=(\mu-r)/\sigma$ and
--   $$\hat a=r+\Big(\frac1{1+\gamma}-\frac12\cdot\frac1{(1+\gamma)^2}\Big)\theta^2 .$$
--   Then
--   $$r<\hat a<r+\tfrac12\theta^2 .$$
--
--   The target annual return of the equilibrium strategy lies strictly between the riskless rate and the growth rate $r+\theta^2/2$ of the log-optimal (Kelly) portfolio.
--
--   **Formalization Note** The hypothesis $\mu\ne r$ is added: for $\mu=r$ one has $\theta=0$ and $\hat a=r$, so the printed open interval would not contain $\hat a$.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. 12, Theorem 2(ii), last sentence

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn
import Definitions.Def_LogMeanVar_Complete_Equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LogMeanVar.Complete

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. 12, Theorem 2(ii), last sentence: `â ∈ (r, r + ½θ²)`, where `θ = (μ - r)/σ`.

**Formalization Note** The hypothesis `μ ≠ r` is added: for `μ = r` one has `θ = 0` and
`â = r`, so the open interval is empty of `â` (a printed slip). -/
theorem theorem_2_ii_range (M : Market) (hM : M.Standing) (hμr : M.μ ≠ M.r) :
    M.r < aHat M ∧ aHat M < M.r + theta M ^ 2 / 2 := by sorry

end LogMeanVar.Complete
