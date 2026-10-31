-- Prove2me | Theorems.Thm_MissionAbort_eq_3_weakConvergence
-- name    : MissionAbort.eq_3_weakConvergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:25.21199+00:00
-- url     : https://prove2.me/theorems/a91eae0c-5dba-451d-a2dc-1f0befc48aaa
-- title:
--   Display (3): the Erlang mixtures $G^{(\lambda)}$ converge weakly to $G$
-- statement:
--   Let $G$ be a probability law on the line with $G((-\infty,0])=0$, let $\zeta>0$, and let $m:\mathbb R\to\mathbb N$ satisfy $m(\lambda)/\lambda\to\infty$ as $\lambda\to\infty$. Write
--   $$
--   G^{(\lambda)}(t)=\sum_{i=1}^{m-1}\Big[G\big(\tfrac i{\lambda-\zeta}\big)-G\big(\tfrac{i-1}{\lambda-\zeta}\big)\Big]E_i^{(\lambda-\zeta)}(t)+\Big[1-G\big(\tfrac{m-1}{\lambda-\zeta}\big)\Big]E_m^{(\lambda-\zeta)}(t).
--   $$
--   Then $G^{(\lambda)}$ is a probability law for every $\lambda>\zeta$ with $m(\lambda)\ge 1$, and for every bounded continuous $f$,
--   $$
--   \int f\,\mathrm dG^{(\lambda)}\longrightarrow\int f\,\mathrm dG\qquad(\lambda\to\infty).
--   $$
--
--   The grid and the Erlang rate are $\lambda-\zeta$, so that the surrogate chain has total rate $\lambda$ out of every transient state. The limit is over $\lambda$.
--
--   Differences from the source:
--   - generalization: $G$ a continuous law with a density on $[0,\infty)$ → any probability law with $G((-\infty,0])=0$; reason: no continuity is needed; such laws with densities satisfy this; $G(0)=0$ gives the weights of (3) mass one
--   - encoding: $T_{12}^{(\lambda)}\sim G^{(\lambda)}$ converges weakly → mass-one clause plus convergence of integrals of bounded continuous functions; reason: this is weak convergence of probability laws; same statement
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, (3), p.12

import Mathlib
import Definitions.Def_MissionAbort_erlangMix

open MeasureTheory ProbabilityTheory Filter Topology

namespace MissionAbort

/-- **Display (3)** (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.12). If `G` is a law on `(0, ∞)`,
`ζ > 0` and `m₁(λ)/λ → ∞`, then (3), whose grid and Erlang rate are `λ − ζ`, is a probability law for
every `λ > ζ` with `m₁(λ) ≥ 1`, and `G⁽λ⁾` converges weakly to `G` as `λ → ∞`.

**Formalization Note.** Weak convergence is stated by bounded continuous test functions. The limit
is over `λ`, not over `λ − ζ`. -/
theorem eq_3_weakConvergence (G : Measure ℝ) [IsProbabilityMeasure G] (hG0 : G (Set.Iic 0) = 0)
    (ζ : ℝ) (hζ : 0 < ζ) (m : ℝ → ℕ)
    (hm : Tendsto (fun lam => (m lam : ℝ) / lam) atTop atTop) :
    (∀ lam, ζ < lam → 0 < m lam → IsProbabilityMeasure (erlangMix G (m lam) (lam - ζ))) ∧
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun lam => ∫ x, f x ∂(erlangMix G (m lam) (lam - ζ))) atTop
        (𝓝 (∫ x, f x ∂G)) := by sorry

end MissionAbort
