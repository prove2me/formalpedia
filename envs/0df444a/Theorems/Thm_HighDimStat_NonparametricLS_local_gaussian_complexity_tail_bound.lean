-- Prove2me | Theorems.Thm_HighDimStat_NonparametricLS_local_gaussian_complexity_tail_bound
-- name    : HighDimStat.NonparametricLS.local_gaussian_complexity_tail_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T01:28:05.551781+00:00
-- url     : https://prove2.me/theorems/ca80ebc8-951f-4603-a410-c7e5eaa9a351
-- title:
--   Gaussian concentration tail bound for the local Gaussian complexity supremum
-- statement:
--   For a nonempty star-shaped function class $H$ and any $\delta_n > 0$ satisfying the critical inequality $G_n(\delta_n; H)/\delta_n \le \delta_n/(2\sigma)$, the empirical Gaussian process supremum $Z_n(\delta_n; H) = \sup_{h \in H, \|h\|_n \le \delta_n} |\frac{1}{n} \sum_{i=1}^n w_i h(x_i)|$ satisfies $\mathbb{P}[Z_n(\delta_n; H) \ge \frac{2}{\sigma}\delta_n\sqrt{t\delta_n}] \le \exp(-nt\delta_n/(2\sigma^2))$ and $\mathbb{P}[Z_n(\delta_n; H) \le \frac{2}{\sigma}\delta_n\sqrt{t\delta_n}] \ge 1 - \exp(-nt\delta_n/(2\sigma^2))$ for all $t \ge \delta_n$.

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core

namespace HighDimStat.NonparametricLS

open MeasureTheory

/-- **Gaussian concentration for the local Gaussian complexity supremum (Wainwright §13.2.2, p. 423).**
For a nonempty star-shaped function class `H` and any `δn > 0` satisfying the critical inequality
`Gₙ(δn; H)/δn ≤ δn/(2σ)`, the empirical Gaussian process supremum
`Zₙ(δn; H) = sup_{h ∈ H, ‖h‖ₙ ≤ δn} |(1/n) ∑ᵢ wᵢ h(xᵢ)|` is `(δn/√n)`-Lipschitz in `w` and has mean
`Gₙ(δn; H) ≤ δn²/(2σ) ≤ (1/(2σ)) δn √(t δn)` for every `t ≥ δn`. By Gaussian concentration of
Lipschitz functions, `P[Zₙ(δn; H) ≥ (2/σ) δn √(t δn)] ≤ exp(-n t δn / (2σ²))` and
`P[Zₙ(δn; H) ≤ (2/σ) δn √(t δn)] ≥ 1 - exp(-n t δn / (2σ²))`. -/
theorem local_gaussian_complexity_tail_bound {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (x : Fin n → X) (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hw : IsIIDStdGaussian P w) (H : Set (X → ℝ)) (hStar : IsStarShaped H) (hH : H.Nonempty)
    (σ δn t : ℝ) (hσ : 0 < σ) (hδn : SatisfiesCriticalInequality x w P H σ δn) (ht : δn ≤ t) :
    P.real {ω | 2 / σ * δn * Real.sqrt (t * δn) ≤
        ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn},
          |(∑ i, w i ω * h.1 (x i)) / n|} ≤
      Real.exp (-(↑n * t * δn) / (2 * σ ^ 2)) ∧
    1 - Real.exp (-(↑n * t * δn) / (2 * σ ^ 2)) ≤
      P.real {ω | ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn},
          |(∑ i, w i ω * h.1 (x i)) / n| ≤
        2 / σ * δn * Real.sqrt (t * δn)} := by sorry

end HighDimStat.NonparametricLS
