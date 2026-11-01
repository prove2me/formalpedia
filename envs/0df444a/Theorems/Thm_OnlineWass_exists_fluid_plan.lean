-- Prove2me | Theorems.Thm_OnlineWass_exists_fluid_plan
-- name    : OnlineWass.exists_fluid_plan
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:35.606554+00:00
-- url     : https://prove2.me/theorems/59346bd0-f0bb-400b-94e4-590f7dda2d4a
-- title:
--   (9)–(10) — a complementary plan exists (corrected: $f(0;\theta)\ge0$, complementary tie-break)
-- statement:
--   Let $\mathcal X,\Theta,f,g,q$ satisfy Assumption 1 with $\rho$ of (2) as the distance of $\Theta$, and suppose $f(0;\theta)\ge0$ for every $\theta$. Let $T\ge1$, $c\ge0$, and let $\hat{\mathcal P}_1,\dots,\hat{\mathcal P}_T$ be probability measures on $\Theta$. Then
--
--   1. $\hat L$ has a minimizer over $p\ge0$;
--   2. for every minimizer $\hat p^*$ of $\hat L$ over $p\ge 0$ there is a map $\hat x$ such that $(\hat p^*,\hat x)$ is a fluid plan.
--
--   This is what makes the input of IGD($\hat\gamma$) well defined: the paper takes (9) and (10) for granted.
--
--   Differences from the source:
--   - correction: Assumption 1 says nothing on f(0;θ); the proofs treat x = 0 as having zero objective value → separate hypothesis f(0;θ) ≥ 0 for every θ; reason: Theorem 3 fails: 𝒳=[0,1], m=1, q=1, Θ a point, W_T=0, g(x)=x, f(x)=−(1−Tx)² on [0,1/T] and 0 beyond, c=1/2 satisfies Assumption 1 and has regret ≈ T/4
--   - correction: (10) writes x̂(θ) = argmax, any maximizer → IsFluidPlan: x̂ a measurable maximizer with Σₜγ̂ₜ ≤ c and (p̂*)ᵀ(c − Σₜγ̂ₜ) = 0; reason: with a free tie-break the bound fails: Θ={a,b}, f(x;a)=x/2, f(x;b)=x, g=x, 𝒳=[0,1], q=1, c=3T/4, θₜ=a for t≤T/2 else b, 𝒫̂=𝒫, W_T=0, x̂(a)=1 gives regret T/8; every minimizer has a complementary x̂ (exists_fluid_plan), and when the argmax is unique it is the printed x̂
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: initial capacity c, sign unstated → every c ≥ 0, including cᵢ = 0; reason: at cᵢ < 0 (PCP) is infeasible; the source's c is a case
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, (9), (10), p.21, corrected

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_dual
import Definitions.Def_OnlineWass_IsFluidPlan

open MeasureTheory

namespace OnlineWass

/-- **Displays (9)–(10) of Jiang, Li & Zhang, arXiv:2012.06961v3, p.21, corrected: a complementary plan
exists.** For every prior `𝒫̂`, `L̂` has a minimizer over `p ≥ 0`, and every such minimizer `p̂*` extends to
a plan `(p̂*, x̂)`.

**Formalization Note.** The paper takes (9)–(10) for granted; this is the statement that the corrected
inputs of IGD(γ̂) exist, so that the goal is not vacuous. -/
theorem exists_fluid_plan {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (q : ℝ) (hA : Assumption1 M q) (hρ : DistEqRho M)
    (hf0 : ∀ θ, 0 ≤ M.f 0 θ) (hT : 0 < T) (c : Fin m → ℝ) (hc : 0 ≤ c)
    (Phat : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (Phat t)] :
    (∃ p, IsDualMinimizer M c Phat p) ∧
      ∀ p, IsDualMinimizer M c Phat p → ∃ xhat, IsFluidPlan M c Phat p xhat := by sorry

end OnlineWass
