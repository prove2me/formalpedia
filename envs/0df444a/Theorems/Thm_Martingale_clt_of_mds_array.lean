-- Prove2me | Theorems.Thm_Martingale_clt_of_mds_array
-- name    : Martingale.clt_of_mds_array
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:37:04.129524+00:00
-- url     : https://prove2.me/theorems/e7143dea-28c4-4a9e-9e6e-0608b0c30ea6
-- title:
--   Martingale CLT (difference-array form)
-- statement:
--   **Martingale central limit theorem.** For each $n$ let $\{D_{n,k} : k < n\}$ be a **martingale difference array** with respect to a filtration $\{\mathcal{F}_k\}$, i.e. $D_{n,k}$ is $\mathcal{F}_k$-measurable and $E[D_{n,k+1} \mid \mathcal{F}_k] = 0$. Suppose
--
--   1. **negligibility of increments:** $\displaystyle E\Bigl[\max_{k<n} |D_{n,k}|\Bigr] \to 0$; and
--   2. **limiting variance:** $\displaystyle \sum_{k<n} D_{n,k}^2 \Rightarrow \sigma^2$.
--
--   Then $\displaystyle \sum_{k<n} D_{n,k} \Rightarrow \sigma N(0,1)$.
--
--   The array formulation carries the normalisation inside the increments, which is why no $\sqrt n$ appears: applied to a stationary difference sequence one takes $D_{n,k} = D_k/\sqrt n$, and the two hypotheses become an $L^1$-negligibility statement and the ergodic-average convergence $n^{-1}\sum_{k<n}D_k^2 \to E[D_0^2]$. Contrast with the Lindeberg–Feller CLT: the conditions are the direct analogues, with independence replaced by the martingale property.
--
--   This is the fundamental limit theorem for dependent sequences and the engine behind central limit theorems for Markov chains, stochastic approximation and time series, via Gordin's martingale-approximation method.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2 and its proof.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem Martingale.clt_of_mds_array {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (D : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n k, Measurable (D n k))
    (hadapt : ∀ n k, Measurable[ℱ k] (D n k))
    (hint : ∀ n k, Integrable (D n k) P)
    (hmds : ∀ n k, P[D n (k + 1) | ℱ k] =ᵐ[P] 0)
    (hcent : ∀ n, ∫ ω, D n 0 ω ∂P = 0)
    (σ : ℝ) (hσ : 0 ≤ σ)
    -- (1) negligibility of increments: `E[max_{k<n} |D n k|] → 0`
    (hneg : Tendsto (fun n : ℕ => ∫ ω, ⨆ k : Fin n, |D n k.val ω| ∂P) atTop (𝓝 0))
    -- (2) limiting variance: `∑_{k<n} (D n k)² ⇒ σ²`
    (hvar : TendstoInMeasure P
      (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, D n k ω ^ 2) atTop (fun _ => σ ^ 2)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, D n k ω)
      atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 (σ ^ 2).toNNReal) := by
  sorry
