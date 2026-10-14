-- Prove2me | Theorems.Thm_OTSensitivity_Info_transportCost_lsc
-- name    : OTSensitivity.Info.transportCost_lsc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:53.45242+00:00
-- url     : https://prove2.me/theorems/64db3eb5-6af3-42fd-808d-3e1711c66b01
-- title:
--   Proof of Theorem 9 — K(ν, ·) is lower semicontinuous under weak convergence
-- statement:
--   Let $\mathsf Y$ be a Polish space and $\mathsf k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ continuous with $\mathsf k(y,y')=0\iff y=y'$, with optimal-transport cost $K$ as in (1). Let $\nu$ be a probability measure on $\mathsf Y$, and let probability measures $\nu_n$ converge weakly to a probability measure $\nu'$ on $\mathsf Y$, i.e. $\int\varphi\,d\nu_n\to\int\varphi\,d\nu'$ for every $\varphi\in C_b(\mathsf Y)$. Then
--   $$K(\nu,\nu')\ \le\ \liminf_{n\to\infty}K(\nu,\nu_n).$$
--
--   In the proof of Theorem 9 this is applied pointwise to $\nu_n=\nu^n_x$, $\nu'=\nu^\infty_x$, and then Fatou's lemma gives the lower bound for $\xi^K(Y,X\mid\mathcal F_n)$.
--
--   **Formalization Note** The liminf is taken in $[0,+\infty]$, so no finiteness is assumed. $K$ is `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 9, p. 36

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTSensitivity.Info

/-- Proof of Theorem 9, p. 36 ("K is lower semicontinuous w.r.t. weak convergence"): if probability
measures `νₙ` converge weakly to `ν'` on `𝓨` (tested against every bounded continuous `φ`), then
`K(ν, ν') ≤ liminf_n K(ν, νₙ)` for every probability measure `ν` on `𝓨`. -/
theorem transportCost_lsc {𝓨 : Type*}
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ν : Measure 𝓨) [IsProbabilityMeasure ν]
    (νs : ℕ → Measure 𝓨) (hνs : ∀ n, IsProbabilityMeasure (νs n))
    (ν' : Measure 𝓨) [IsProbabilityMeasure ν']
    (hconv : ∀ φ : 𝓨 →ᵇ ℝ, Tendsto (fun n => ∫ y, φ y ∂(νs n)) atTop (𝓝 (∫ y, φ y ∂ν'))) :
    RWPI.SqrtLasso.transportCost k ν ν'
      ≤ liminf (fun n => RWPI.SqrtLasso.transportCost k ν (νs n)) atTop := by sorry

end OTSensitivity.Info
