-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_lemma_5_3
-- name    : JSEQDelay.Diffusion.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:21.302189+00:00
-- url     : https://prove2.me/theorems/61e4f51f-a863-4f18-b7d1-95ab8f4b3664
-- title:
--   Lemma 5.3, p. 20 — state space collapse: P(θⁿ < T) → 0, C-tightness of (Âⁿ, Q̂ⁿ, L̂ⁿ, M̂ⁿ), Δ̂ⁿ → 0
-- statement:
--   Under the hypotheses of Lemma 5.2 (primitives, heavy traffic, Assumptions 3.1 and 3.8, JSEQ networks):
--
--   1. for every $T\in(0,\infty)$ there is a sequence $r_n>0$, $r_n\to0$, such that with $\theta^n$ defined by (47), $\mathbb P(\theta^n<T)\to0$;
--   2. the sequence $(\hat A^n,\hat Q^n,\hat L^n,\hat M^n)$ is C-tight;
--   3. $\hat\Delta^n\to0$ in probability:
--   $$\mathbb P\Big(\sup_{0\le t\le T}|\hat\Delta^n(t)|\ge\varepsilon\Big)\to0\qquad\text{for all }T,\varepsilon>0 .$$
--
--   This is state space collapse for the estimated queue lengths: in the limit all estimates coincide, which becomes equation (41) of the diffusion model.
--
--   **Formalization Note** "In probability" for a process with a continuous (zero) limit is read as uniformly on compacts in probability (published `UocInProb`). C-tightness is `IsCTight` as in Lemma 5.2. The proof on p. 20 asserts that the jumps of $\hat M^n$ are $O(n^{-1/2})$; this does not follow from Assumption 3.8, but the lemma's freedom to choose $(r_n)$ absorbs the gap.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 20, Lemma 5.3

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_JSEQDelay_Diffusion_Model
import Definitions.Def_JSEQDelay_Diffusion_Assumptions
import Definitions.Def_JSEQDelay_Diffusion_Collapse

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-- **Lemma 5.3** (state space collapse, p. 20): under Assumption 3.1 on the delay function
and Assumption 3.8 on the scaled estimators,
1. for every `T ∈ (0, ∞)` there is `(rₙ) ∈ 𝒵` such that, with `θⁿ` defined by (47),
   `P(θⁿ < T) → 0`;
2. the sequence `(Âⁿ, Q̂ⁿ, L̂ⁿ, M̂ⁿ)` is C-tight;
3. `Δ̂ⁿ → 0` in probability (uniformly on compact time intervals). -/
theorem lemma_5_3 {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (α : ℝ) (γ : Fin K → ℝ)
    (hprim : Primitives P u v α γ)
    (lam : ℕ → ℝ) (mu : ℕ → Fin K → ℝ) (lamBar lamHat : ℝ) (muBar muHat : Fin K → ℝ)
    (hrates : Rates lam mu) (hHT : HeavyTraffic lam mu lamBar lamHat muBar muHat)
    (τ : ℝ → Fin K → ℝ) (hτ : Assumption31 τ)
    (Ψ : ℕ → Path K → Path K → Path K) (hΨ : ∀ n, IsEstimator τ (Ψ n))
    (h38 : Assumption38 τ (fun n => PsiHat n (mu n) (Ψ n)))
    (Q A : ℕ → Ω → Path K)
    (hnet : ∀ n, 1 ≤ n → IsJSEQNetwork u v (lam n) (mu n) τ (Ψ n) (Q n) (A n)) :
    (∀ T : ℝ, 0 < T → ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      Tendsto (fun n => P {ω | theta (r n) (Delta n (mu n) τ (Ψ n) (Q n) (A n)) ω <
        ENNReal.ofReal T}) atTop (𝓝 0)) ∧
    IsCTight P (fun n => quad n (mu n) (Ψ n) (Q n) (A n)) ∧
    UocInProb P (fun n ω t (_ : Fin 1) => Delta n (mu n) τ (Ψ n) (Q n) (A n) ω t)
      (fun _ _ => 0) := by sorry

end JSEQDelay.Diffusion
