-- Prove2me | Theorems.Thm_LogMeanVar_Complete_c2_moments_deterministic
-- name    : LogMeanVar.Complete.c2_moments_deterministic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:40.020362+00:00
-- url     : https://prove2.me/theorems/815c30df-f243-4df9-b283-90bd1146af32
-- title:
--   Proof of Theorem 2 (App. C.2), p. O–10 — for a deterministic policy, E_t[R_T] = R_t + ∫_t^T (r + π_s(µ−r) − ½π_s²σ²) ds and Var_t(R_T) = ∫_t^T π_s²σ² ds
-- statement:
--   Consider the complete market with $\sigma>0$, $\gamma>0$, $T>0$, and a real Brownian motion $B$ on a probability space. Let $p:\mathbb R\to\mathbb R$ be measurable and consider the **deterministic** policy $\pi(\tau,y)=p(\tau)$. Let $t\in[0,T)$, $y\in\mathbb R$, and let $R$ be any solution of the log-return equation (6) under this policy, started at $R_t=y$. Then $R_T$ is square integrable and
--   $$\mathbb E[R_T]=y+\int_t^T\Big(r+p(s)(\mu-r)-\tfrac12 p(s)^2\sigma^2\Big)ds,\qquad \mathrm{Var}(R_T)=\int_t^T p(s)^2\sigma^2\,ds .$$
--
--   This is the moment computation on which the whole proof of Theorem 2 rests: it reduces the reward of any deterministic strategy to a deterministic integral.
--
--   **Formalization Note** Square integrability of $p$ on $[t,T]$ is part of being a solution of (6). The square-integrability conclusion makes the two identities meaningful (Lean's integral and variance are $0$ on non-integrable inputs). The coordinates of $B$ are assumed measurable (a Brownian motion is a family of random variables).
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. O-10, Proof of Theorem 2 (App. C.2), first sentence

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn
import Definitions.Def_LogMeanVar_Complete_Equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LogMeanVar.Complete

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. O–10, Proof of Theorem 2 (App. C.2), first sentence: for a deterministic trading
policy `π_s = p(s)`, every solution `R` of (6) started at `R_t = y`, `t ∈ [0, T)`, has
`R_T ∈ L²`, `E_t[R_T] = R_t + ∫_t^T (r + p(s)(μ - r) - ½p(s)²σ²) ds` and
`Var_t(R_T) = ∫_t^T p(s)²σ² ds`.

**Formalization Note** "Deterministic" means `π τ y = p τ` with `p` measurable; square
integrability of `p` on `[t, T]` is part of `IsLogReturn`. `E_t`, `Var_t` are the moments of
the process started at `(t, y)`. The `L²` conclusion makes the two moment identities
non-junk. -/
theorem c2_moments_deterministic (M : Market) (hM : M.Standing) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P)
    (hBm : ∀ s, Measurable (B s)) (p : ℝ → ℝ) (hp : Measurable p) (t : ℝ) (ht : t ∈ Ico 0 M.T)
    (y : ℝ) (R : ℝ → Ω → ℝ) (hR : IsLogReturn M P B (fun τ _ => p τ) t y R) :
    MemLp (R M.T) 2 P ∧
      ∫ ω, R M.T ω ∂P =
        y + ∫ s in t..M.T, (M.r + p s * (M.μ - M.r) - 1 / 2 * p s ^ 2 * M.σ ^ 2) ∧
      variance (R M.T) P = ∫ s in t..M.T, p s ^ 2 * M.σ ^ 2 := by sorry

end LogMeanVar.Complete
