-- Prove2me | Theorems.Thm_LearnStability_ConvexSCO_theorem2_strongly_convex_erm
-- name    : LearnStability.ConvexSCO.theorem2_strongly_convex_erm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:17:19.478904+00:00
-- url     : https://prove2.me/theorems/1699f3f3-9496-4d5b-ba00-08ef0e461fa5
-- title:
--   Theorem 2: the strongly convex empirical minimizer has $F(\hat h_S)-F^*\le 4L^2/(\delta\lambda m)$ with probability $1-\delta$
-- statement:
--   Consider a stochastic convex optimization problem on $\mathcal H$ (nonempty, closed, convex, bounded, in a real Hilbert space) whose objective $f(h;z)$ is, for every $z$, $\lambda$-strongly convex ($\lambda>0$) and $L$-Lipschitz with respect to $h\in\mathcal H$, with $|f|\le C$. Let $z_1,\dots,z_m$ ($m\ge1$) be an i.i.d. sample from a distribution $D$ and let $\hat h_S$ be the empirical minimizer of $F_S$ over $\mathcal H$. Then for every $\delta\in(0,1)$, with probability at least $1-\delta$ over the sample,
--   $$F(\hat h_S)-F^*\ \le\ \frac{4L^2}{\delta\lambda m}.$$
--
--   In infinite dimension uniform convergence can fail for such problems (§4.1–4.2), so this learnability guarantee comes from stability rather than from uniform convergence.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as $D^m\{S: F(\hat h_S)-F^*>4L^2/(\delta\lambda m)\}\le\delta$. The empirical minimizer is any selection $S\mapsto\hat h_S\in\mathcal H$ of minimizers with $(S,z)\mapsto f(\hat h_S;z)$ jointly measurable (series convention, not in the paper).
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2644, Theorem 2

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting
import Definitions.Def_LearnStability_ConvexSCO_Problem

open MeasureTheory

namespace LearnStability.ConvexSCO

/-- Theorem 2 (p. 2644): for a stochastic convex optimization problem whose objective is
`λ`-strongly convex (`λ > 0`) and `L`-Lipschitz in `h ∈ H`, every measurable selection of
empirical minimizers `ĥ_S` over `H` satisfies, for every distribution `D`, every `m ≥ 1` and
every `δ ∈ (0,1)`, `F(ĥ_S) − F* ≤ 4L²/(δλm)` with probability at least `1 − δ` over
`S ∼ D^m`; stated as a bound `≤ δ` on the probability of the failure event. -/
theorem theorem2_strongly_convex_erm {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {f : E → Z → ℝ} {L C lam : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hlam : 0 < lam)
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z))
    (D : Measure Z) [IsProbabilityMeasure D] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {m : ℕ} (hm : 1 ≤ m) (hhat : (Fin m → Z) → E) (hmin : IsEmpMinimizerOn Hset f hhat)
    (hmeas : IsMeasurableSelection f hhat) :
    sampleLaw D m {S | 4 * L ^ 2 / (δ * lam * m) < risk f D (hhat S) - optRiskOn Hset f D} ≤
      ENNReal.ofReal δ := by sorry

end LearnStability.ConvexSCO
