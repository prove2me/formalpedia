-- Prove2me | Theorems.Thm_MissionAbort_eq_2_weakConvergence
-- name    : MissionAbort.eq_2_weakConvergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:28.573999+00:00
-- url     : https://prove2.me/theorems/22e02893-b6dd-4463-b80d-4ff0f909c30f
-- title:
--   Display (2): the Erlang mixtures $F^{(\lambda)}$ converge weakly to $F$
-- statement:
--   Let $F$ be a probability law on the line with $F((-\infty,0])=0$, and let $m:\mathbb R\to\mathbb N$ satisfy $m(\lambda)/\lambda\to\infty$ as $\lambda\to\infty$. Write
--   $$
--   F^{(\lambda)}(t)=\sum_{i=1}^{m-1}\Big[F\big(\tfrac i\lambda\big)-F\big(\tfrac{i-1}\lambda\big)\Big]E_i^{(\lambda)}(t)+\Big[1-F\big(\tfrac{m-1}\lambda\big)\Big]E_m^{(\lambda)}(t),
--   $$
--   with $E_i^{(\lambda)}$ the Erlang CDF of rate $\lambda$ and shape $i$. Then $F^{(\lambda)}$ is a probability law for every $\lambda>0$ with $m(\lambda)\ge 1$, and for every bounded continuous $f$,
--   $$
--   \int f\,\mathrm dF^{(\lambda)}\longrightarrow\int f\,\mathrm dF\qquad(\lambda\to\infty).
--   $$
--
--   This is the approximation of the sojourn time $T_{23}$ by the phase-type surrogate. The paper cites it from Corollary 4.1 of Wiens (1979).
--
--   Differences from the source:
--   - generalization: $F$ a continuous law with a density on $[0,\infty)$ → any probability law with $F((-\infty,0])=0$; reason: no continuity is needed; such laws with densities satisfy this; $F(0)=0$ is what gives the weights of (2) mass one (p.EC.1)
--   - encoding: the random variable with CDF (2) converges weakly → mass-one clause plus convergence of integrals of bounded continuous functions; reason: this is weak convergence of probability laws; same statement
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, (2), p.12, citing Corollary 4.1 of Wiens (1979)

import Mathlib
import Definitions.Def_MissionAbort_erlangMix

open MeasureTheory ProbabilityTheory Filter Topology

namespace MissionAbort

/-- **Display (2)** (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.12, citing Corollary 4.1 of Wiens
(1979)). If `F` is a law on `(0, ∞)` and `m₂(λ)/λ → ∞`, then (2) is a probability law for every
`λ > 0` with `m₂(λ) ≥ 1`, and `F⁽λ⁾` converges weakly to `F` as `λ → ∞`.

**Formalization Note.** Weak convergence is stated by bounded continuous test functions, as in
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. `F (Iic 0) = 0` is what makes the weights of
(2) sum to one (the proof on p.EC.1 uses "`F(0) = 0`"). `F` need not be continuous here. -/
theorem eq_2_weakConvergence (F : Measure ℝ) [IsProbabilityMeasure F] (hF0 : F (Set.Iic 0) = 0)
    (m : ℝ → ℕ) (hm : Tendsto (fun lam => (m lam : ℝ) / lam) atTop atTop) :
    (∀ lam, 0 < lam → 0 < m lam → IsProbabilityMeasure (erlangMix F (m lam) lam)) ∧
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun lam => ∫ x, f x ∂(erlangMix F (m lam) lam)) atTop (𝓝 (∫ x, f x ∂F)) := by sorry

end MissionAbort
