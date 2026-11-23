-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_Supplement_theorem_5_counterexample
-- name    : MarketInterference.FluidBias.Supplement.theorem_5_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:48:10.149394+00:00
-- url     : https://prove2.me/theorems/35fef86e-fc3c-4258-bb2c-b67c64f69965
-- title:
--   Theorem 5 — auxiliary companion (corrected: raw RCT variance-limit counterexample)
-- statement:
--   The conditional-mean blindness equation in Assumption 1 is insufficient for the RCT variance limit asserted in Theorem 5. Consider one demand type, one supply type and one arc of value $1$ and capacity $3$. Set $\lambda=2$, $\beta=0$, $\pi=1$ and $\rho=1/2$. The fluid optimal primal and whole dual are unique. At density $n$, independently draw $C,T,S\sim\operatorname{Poisson}(n)$ and an independent uniform allocation seed. With $M=\min(C+T,S,3n)$, match $K$ controls and $M-K$ treated units. For even $n$, randomly round $m=MC/(C+T)$ to adjacent integers; for odd $n$, use the two feasible extremes $L=\max(0,M-T)$ and $U=\min(M,C)$, with upper probability $(m-L)/(U-L)$. Both rules have exactly the mean $m$ required by Assumption 1.
--
--   There exist path allocations realizing this specified rule, satisfying the actual source experiment law, optimality, group-count bounds and blindness. Every scaled RCT variable is square integrable. Nevertheless, writing
--   $$
--   V_n=\operatorname{Var}\!\left[\sqrt n\,\widehat\Delta^n_{RCT}\right],
--   \qquad\widehat\Delta^n_{RCT}=\frac{2(M-2K)}n,
--   $$
--   one has
--   $$
--   V_{2m}\longrightarrow2,\qquad V_{2m+1}\longrightarrow+\infty.
--   $$
--   In particular the RCT variance has no real limit (nor an extended-real limit), so the displayed comparison in Theorem 5 cannot be asserted for all allocations admitted by its formal assumptions. This is a counterexample to the existence component, not a reversed inequality in an experiment with existing limits. `DISPROOF.md` gives the conditional-variance calculation and the source evidence.
--
--   **Formalization Note** The theorem constructs actual integer-valued group allocations, and uses the real variance only with an explicit square-integrability conclusion. It has no assumptions: uniqueness and validity of the experiment are part of its conclusion. The array index $n$ in Lean represents density $n+1$, so even densities appear at array indices $2n+1$. A uniform-subset allocation law would exclude this construction, but that stronger law is absent from the source's displayed Assumption 1. The estimator here is the raw RCT estimator of Definition 2, the one whose variance the proof of Theorem 5 decomposes by the law of total variance in (30) on p. 47. A remark on p. 42 says the paper's results analyze the variance-reduced version $\mathbb E[\widehat\Delta^\tau_{RCT}\mid D^{\tau,control},D^{\tau,treatment},S^\tau]$ instead. Under that reading the allocation randomness, and with it this counterexample, disappears. The variance-reduced reading is separately refuted by the different routing construction in `theorem_5`; the present auxiliary statement concerns only the raw estimator. The coefficient-freezing step of the source proof is not installed as a premise; proofs remain downstream work.
--
--   Differences from the source:
--   - correction: Assumptions 1–2 ensure the displayed asymptotic variance limits and comparison → an explicit admissible one-arc allocation has RCT variance tending to 2 along even densities and diverging along odd densities; reason: Assumption 1 fixes only E[K|C,T,S]=MC/(C+T), not conditional second moments; the construction in DISPROOF.md obeys that equation and has unique fluid optima
--   - encoding: variance of the density-indexed estimators → Mathlib real variance on square-integrable variables at density n+1; reason: the positive index avoids zero-density division, and square integrability prevents infinite-variance default values
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 23, Theorem 5 and (13); p. 11, Assumption 1; pp. 47–48, proof

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_Supplement_RandomAllocation

namespace MarketInterference.FluidBias.Supplement

open MeasureTheory Filter

/-- Assumptions 1 and 2 alone do not imply existence of the displayed RCT variance limit. -/
theorem theorem_5_counterexample :
    (∃! x, IsOptimal varianceNetwork 1 (fun _ => 2) (fun _ => 1) x) ∧
    (∃! q, IsOptimalDual varianceNetwork 1 (fun _ => 2) (fun _ => 1) q) ∧
    (∀ n, IsProbabilityMeasure (varianceLaw (n + 1)) ∧
      HasExperimentLaw (varianceLaw (n + 1)) Prod.fst (fun _ => 2) (fun _ => 0)
        (fun _ => 1) (1/2) (n + 1 : ℕ)) ∧
    ∃ A : ∀ n : ℕ, BlindAllocation varianceNetwork (varianceLaw (n + 1)) Prod.fst (n + 1 : ℕ),
      (∀ n, ∀ᵐ ω ∂varianceLaw (n + 1), (A n).total ω =
        Finsupp.single variancePath (matchedCount (n + 1) ω.1 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂varianceLaw (n + 1),
        (A n).control ω = Finsupp.single variancePath (alternatingControl (n + 1) ω : ℝ) ∧
        (A n).treatment ω = Finsupp.single variancePath
          ((matchedCount (n + 1) ω.1 : ℝ) - (alternatingControl (n + 1) ω : ℝ))) ∧
      (∀ n, MemLp (fun ω => Real.sqrt (n + 1 : ℕ) *
        rctEst varianceNetwork (varianceLaw (n + 1)) Prod.fst (1/2) (n + 1 : ℕ) (A n) ω)
        2 (varianceLaw (n + 1))) ∧
      (let V := fun n => rctScaledVariance varianceNetwork (varianceLaw (n + 1))
        Prod.fst (1/2) (n + 1 : ℕ) (A n)
       Tendsto (fun n => V (2 * n + 1)) atTop (nhds 2) ∧
       Tendsto (fun n => V (2 * n)) atTop atTop ∧
       ¬ ∃ v : ℝ, Tendsto V atTop (nhds v)) := by sorry

end MarketInterference.FluidBias.Supplement
