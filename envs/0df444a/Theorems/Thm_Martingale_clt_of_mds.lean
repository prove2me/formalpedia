-- Prove2me | Theorems.Thm_Martingale_clt_of_mds
-- name    : Martingale.clt_of_mds
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:32:47.124927+00:00
-- url     : https://prove2.me/theorems/17b4ea00-5d1d-45f3-b0c6-60104c858cef
-- title:
--   Martingale central limit theorem (Brown-McLeish, Lindeberg form)
-- statement:
--   **The martingale central limit theorem.** Let $\{D_i\}_{i \ge 0}$ be a sequence of square-integrable random variables adapted to a filtration $\{\mathcal{F}_i\}$ and forming a **martingale difference sequence**, i.e.
--
--   $$E\bigl[D_{i+1} \mid \mathcal{F}_i\bigr] = 0 \quad \text{a.s. for every } i,$$
--
--   with $E[D_0] = 0$. Suppose the normalised quadratic variation stabilises,
--
--   $$\frac{1}{n}\sum_{i<n} D_i^2 \;\xrightarrow{\;\mathbb{P}\;}\; v \ge 0,$$
--
--   and that the **Lindeberg condition** holds: for every $\varepsilon > 0$,
--
--   $$\frac{1}{n}\sum_{i<n} E\Bigl[D_i^2 \,\mathbf{1}\{|D_i| \ge \varepsilon\sqrt n\}\Bigr] \longrightarrow 0 .$$
--
--   Then the normalised partial sums are asymptotically Gaussian:
--
--   $$\frac{1}{\sqrt n}\sum_{i<n} D_i \;\xrightarrow{d}\; N(0, v).$$
--
--   This is the fundamental limit theorem for dependent sequences, generalising the classical Lindeberg CLT (which is the special case of an independent sequence, where the conditioning is trivial and the quadratic-variation condition is the law of large numbers). It is the engine behind essentially every central limit theorem for Markov chains, stochastic approximation, and time series, since Gordin's martingale-approximation method reduces those to this statement.
--
--   **Proof route (Brown 1971; McLeish 1974; Hall & Heyde 1980, Theorem 3.2).** One shows $E[e^{itS_n/\sqrt n}] \to e^{-t^2v/2}$ and appeals to Lévy's continuity theorem. Independence is unavailable, so the characteristic function cannot be factored into a product; McLeish's device is to compare $e^{itS_n/\sqrt n}$ with the product $\prod_{i<n}(1 + itD_i/\sqrt n)$, which *is* telescoping-friendly because each factor has conditional expectation $1$ given the past — this is exactly where the martingale difference property enters. The Lindeberg condition makes the individual increments asymptotically negligible so that the logarithm of the product can be expanded to second order, and the quadratic-variation hypothesis identifies the resulting sum $-\tfrac{t^2}{2n}\sum_i D_i^2$ with $-t^2v/2$ in the limit.
--
--   Stated in the Lindeberg form rather than with a conditional-variance hypothesis because the Lindeberg sum is unconditional and therefore easier to verify: for a *stationary* difference sequence with $D_0 \in L^2$ it reduces by stationarity to $E[D_0^2\mathbf{1}\{|D_0| \ge \varepsilon\sqrt n\}] \to 0$, which is dominated convergence, while the quadratic-variation condition follows from the pointwise ergodic theorem.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem Martingale.clt_of_mds {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hadapt : Adapted ℱ D) (hmeas : ∀ i, Measurable (D i))
    (hL2 : ∀ i, MemLp (D i) 2 P)
    (hcent : ∫ ω, D 0 ω ∂P = 0)
    (hmds : ∀ i, P[D (i + 1) | ℱ i] =ᵐ[P] 0)
    (v : ℝ) (hv : 0 ≤ v)
    (hqv : TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, D i ω ^ 2) atTop (fun _ => v))
    (hlind : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ∫ ω, Set.indicator {ω' | ε * Real.sqrt n ≤ |D i ω'|} (fun ω' => D i ω' ^ 2) ω ∂P)
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, D i ω)
      atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 v.toNNReal) := by sorry
