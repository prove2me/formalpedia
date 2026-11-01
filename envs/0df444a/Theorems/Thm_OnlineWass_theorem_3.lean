-- Prove2me | Theorems.Thm_OnlineWass_theorem_3
-- name    : OnlineWass.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:20.880407+00:00
-- url     : https://prove2.me/theorems/c4b39146-9e4f-4bee-aecf-ef83248fdb60
-- title:
--   Theorem 3 — IGD($\hat\gamma$) has regret $O(\max\{\sqrt T,W_T\})$ (corrected: $f(0;\theta)\ge0$, complementary tie-break in (10))
-- statement:
--   Let $\mathcal X\subset\mathbb R^k$ be compact and convex with $0\in\mathcal X$, let $\Theta$ be a metric Borel space with $\rho$ of (2) as its distance, and let $f,g,q$ satisfy Assumption 1, with $f(0;\theta)\ge0$ for every $\theta$. Let $T\ge1$, $c\ge0$, and let $\hat{\mathcal P}_1,\dots,\hat{\mathcal P}_T$ be probability measures on $\Theta$. Then:
--
--   1. **The inputs exist.** $\hat L$ has a minimizer over $p\ge0$; every minimizer extends to a fluid plan $(\hat p^*,\hat x)$; and a tie-break rule exists.
--   2. **The bound.** For every fluid plan, every tie-break rule, every $W_T\ge0$ and all probability measures $\mathcal P_1,\dots,\mathcal P_T$ with $\sum_t\mathcal W(\mathcal P_t,\hat{\mathcal P}_t)\le W_T$, let $\pi$ be the run of IGD($\hat\gamma$) and let $\mathcal H\sim\mathcal P_1\otimes\dots\otimes\mathcal P_T$. Then $R^*_T$ and $R_T(\pi)$ are integrable, and
--
--   $$
--   \mathbb E[R^*_T-R_T(\pi)]\le\Bigl(\frac m2+mq(q+1)\Bigr)\sqrt T+qm+2(q+1)(m+1)\,W_T\le C\max\{\sqrt T,W_T\},
--   $$
--
--   where $C=\frac m2+mq(q+1)+qm+2(q+1)(m+1)$ depends on $m$ and $q$ only.
--
--   The algorithm uses neither $\mathcal P$ nor $W_T$: the same run is good for every law in the Wasserstein ball around the prior. By Theorem 2 of the paper the rate cannot be improved.
--
--   Differences from the source:
--   - correction: Assumption 1 says nothing on f(0;θ); the proofs treat x = 0 as having zero objective value → separate hypothesis f(0;θ) ≥ 0 for every θ; reason: Theorem 3 fails: 𝒳=[0,1], m=1, q=1, Θ a point, W_T=0, g(x)=x, f(x)=−(1−Tx)² on [0,1/T] and 0 beyond, c=1/2 satisfies Assumption 1 and has regret ≈ T/4
--   - correction: (10) writes x̂(θ) = argmax, any maximizer → IsFluidPlan: x̂ a measurable maximizer with Σₜγ̂ₜ ≤ c and (p̂*)ᵀ(c − Σₜγ̂ₜ) = 0; reason: with a free tie-break the bound fails: Θ={a,b}, f(x;a)=x/2, f(x;b)=x, g=x, 𝒳=[0,1], q=1, c=3T/4, θₜ=a for t≤T/2 else b, 𝒫̂=𝒫, W_T=0, x̂(a)=1 gives regret T/8; every minimizer has a complementary x̂ (exists_fluid_plan), and when the argmax is unique it is the printed x̂
--   - reading: O(·) unqualified → constants depending on m and q only; reason: the strongest reading, and what (32)+(33) give; no relation between T and c is assumed
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: Theorem 3 takes (9)–(10) as given → clause 1: the inputs exist for every prior; reason: the theorem is not vacuous, and clause 2 is the printed claim
--   - generalization: initial capacity c, sign unstated → every c ≥ 0, including cᵢ = 0; reason: at cᵢ < 0 (PCP) is infeasible; the source's c is a case
--   - generalization: x̃ₜ = argmax with no rule for ties → any jointly measurable tie-break rule sel; reason: every solver of line 4 that reads (pₜ, θₜ) is such a rule, and the bound holds for each
--   - encoding: Reg_T(π) = max over Ξ_P(W_T) of an expectation; O(·) → the bound for every 𝒫 in the set; explicit constants, with the last inequality as the printed form; reason: a maximum is bounded iff each term is; explicit constants imply O(·)
--   - encoding: R*_T and h as maxima, 𝒲 a real infimum → real sSup over nonempty bounded sets; 𝒲 in ℝ≥0∞ with edist; reason: the maxima are attained by compactness; same values
--   - encoding: periods t = 1, …, T, p₁, p_{T+1} → t : Fin T is period t + 1; p₁ is index 0, p_{T+1} is index T; reason: Lean indices; same instances
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Theorem 3, p.22; proof pp.55–57

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_wasserstein
import Definitions.Def_OnlineWass_dual
import Definitions.Def_OnlineWass_IsFluidPlan
import Definitions.Def_OnlineWass_igd
import Definitions.Def_OnlineWass_benchmarks

open MeasureTheory

namespace OnlineWass

open scoped ENNReal in
/-- **Theorem 3, Jiang, Li & Zhang, arXiv:2012.06961v3, p.22 (proof pp.55–57):** "Under Assumption 1,
suppose a prior estimate 𝒫̂ is available and the regret is defined based on the set Ξ_P(W_T), then the
regret of IGD(γ̂) has the following upper bound Reg_T(π_IGDP) ≤ O(max{√T, W_T})".

Corrected, with `f(0; θ) ≥ 0` and a complementary tie-break in (10). For every horizon `T ≥ 1`, budget
`c ≥ 0` and prior `𝒫̂`: (a) the inputs of IGD(γ̂) exist: `L̂` has a minimizer, every minimizer extends to a
plan, and a tie-break rule exists. (b) For every plan and every tie-break rule, every `W_T ≥ 0` and every
`𝒫` with `Σₜ 𝒲(𝒫ₜ, 𝒫̂ₜ) ≤ W_T`, under `ℙ = ⊗ₜ𝒫ₜ`, `R*_T` and `R_T(π)` are integrable and
`𝔼[R*_T − R_T(π)] ≤ (m/2 + mq(q + 1))√T + qm + 2(q + 1)(m + 1) W_T ≤ C max{√T, W_T}` with
`C = m/2 + mq(q + 1) + qm + 2(q + 1)(m + 1)`.

**Formalization Note.** The regret (3) with a maximum over `Ξ_P(W_T)` is the bound for every `𝒫` in that
set. The constants are (32) + (33). `C` depends on `m` and `q` only. The plan and `sel` are quantified
before `𝒫` and `W_T`, because the algorithm uses neither. -/
theorem theorem_3 {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (q : ℝ) (hA : Assumption1 M q) (hρ : DistEqRho M)
    (hf0 : ∀ θ, 0 ≤ M.f 0 θ) (hT : 0 < T) (c : Fin m → ℝ) (hc : 0 ≤ c)
    (Phat : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (Phat t)] :
    ((∃ p, IsDualMinimizer M c Phat p) ∧
      (∀ p, IsDualMinimizer M c Phat p → ∃ xhat, IsFluidPlan M c Phat p xhat) ∧
      ∃ sel, IsTieBreak M sel) ∧
    ∀ (phat : Fin m → ℝ) (xhat : Θ → Fin k → ℝ), IsFluidPlan M c Phat phat xhat →
    ∀ (sel : (Fin m → ℝ) → Θ → Fin k → ℝ), IsTieBreak M sel →
    ∀ (WT : ℝ), 0 ≤ WT →
    ∀ (P : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (P t)],
      deviationBudget P Phat ≤ ENNReal.ofReal WT →
      Integrable (fun H => offlineValue M c H) (Measure.pi P) ∧
      Integrable (fun H => onlineReward M sel (gammaHat M Phat xhat) c H) (Measure.pi P) ∧
      ∫ H, (offlineValue M c H - onlineReward M sel (gammaHat M Phat xhat) c H) ∂Measure.pi P ≤
        ((m : ℝ) / 2 + (m : ℝ) * q * (q + 1)) * √(T : ℝ) + q * (m : ℝ) +
          2 * (q + 1) * ((m : ℝ) + 1) * WT ∧
      ∫ H, (offlineValue M c H - onlineReward M sel (gammaHat M Phat xhat) c H) ∂Measure.pi P ≤
        ((m : ℝ) / 2 + (m : ℝ) * q * (q + 1) + q * (m : ℝ) + 2 * (q + 1) * ((m : ℝ) + 1)) *
          max (√(T : ℝ)) WT := by sorry

end OnlineWass
