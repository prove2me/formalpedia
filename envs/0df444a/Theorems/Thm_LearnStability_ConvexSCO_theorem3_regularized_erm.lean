-- Prove2me | Theorems.Thm_LearnStability_ConvexSCO_theorem3_regularized_erm
-- name    : LearnStability.ConvexSCO.theorem3_regularized_erm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:18:58.87252+00:00
-- url     : https://prove2.me/theorems/44d4642b-870c-48ed-82dc-4dc40f6b5d6c
-- title:
--   Theorem 3: Tikhonov-regularized ERM has $F(\hat h_\lambda)-F^*\le 4\sqrt{L^2B^2/(\delta m)}\,(1+8/(\delta m))$ with probability $1-\delta$
-- statement:
--   Let $\mathcal H$ be a nonempty, closed, convex subset of a real Hilbert space $E$ with $\|h\|\le B$ for all $h\in\mathcal H$, and let $f(h;z)$ be convex and $L$-Lipschitz in $h\in\mathcal H$ for every instance $z$, with $|f|\le C$ and each $f(h;\cdot)$ measurable ($L,B>0$). Let $D$ be a distribution on $Z$, $\delta\in(0,1)$, $m\ge1$, and let $z_1,\dots,z_m$ be an i.i.d. sample from $D$. Let $\hat h_\lambda$ be the minimizer of
--   $$\hat h_\lambda=\operatorname*{arg\,min}_{h\in\mathcal H}\Big(\frac1m\sum_{i=1}^m f(h,z_i)+\frac\lambda2\|h\|^2\Big)\qquad\text{with}\quad \lambda=\sqrt{\frac{16L^2}{\delta B^2m}}.$$
--   Then, with probability at least $1-\delta$,
--   $$F(\hat h_\lambda)-F^*\ \le\ 4\sqrt{\frac{L^2B^2}{\delta m}}\Big(1+\frac{8}{\delta m}\Big),\qquad F^*=\inf_{h\in\mathcal H}F(h).$$
--
--   Every convex, Lipschitz, bounded stochastic optimization problem in a Hilbert space is therefore learnable, with an explicit rate, even when uniform convergence fails and plain empirical minimization does not converge (§4.1).
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as $D^m\{S: F(\hat h_\lambda)-F^*>\text{bound}\}\le\delta$. The paper's standing loss bound (called $B$ on p. 2637) is named $C$ here, since $B$ is Theorem 3's norm bound. $L>0$ and $B>0$ are implicit on the page (they make $\lambda$ well defined and positive) and are stated. The minimizer is any selection $S\mapsto\hat h_\lambda\in\mathcal H$ of minimizers of (5) for this $\lambda$, with $(S,z)\mapsto f(\hat h_\lambda;z)$ jointly measurable (series convention, not in the paper). $E$ is an arbitrary, possibly infinite-dimensional, real Hilbert space.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2644, Theorem 3 (Eq. (5))

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting
import Definitions.Def_LearnStability_ConvexSCO_Problem

open MeasureTheory

namespace LearnStability.ConvexSCO

/-- Theorem 3 (p. 2644): let `H` be a nonempty, closed, convex subset of a Hilbert space with
`‖h‖ ≤ B` on `H`, and let `f(h, z)` be convex and `L`-Lipschitz in `h ∈ H` (`L, B > 0`), with
`|f| ≤ C`. For every distribution `D`, every `δ ∈ (0,1)`, every `m ≥ 1`, with
`λ = √(16L²/(δB²m))`, every measurable selection `ĥ_λ` of minimizers over `H` of
`F_S(h) + (λ/2)‖h‖²` (Eq. (5)) satisfies, with probability at least `1 − δ` over `S ∼ D^m`,
`F(ĥ_λ) − F* ≤ 4√(L²B²/(δm)) (1 + 8/(δm))`; stated as a bound `≤ δ` on the probability of the
failure event. -/
theorem theorem3_regularized_erm {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {f : E → Z → ℝ} {L C B : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hL : 0 < L) (hBpos : 0 < B)
    (hB : ∀ h ∈ Hset, ‖h‖ ≤ B) (D : Measure Z) [IsProbabilityMeasure D]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {m : ℕ} (hm : 1 ≤ m)
    (hhat : (Fin m → Z) → E)
    (hmin : IsRegMinimizerOn Hset f (Real.sqrt (16 * L ^ 2 / (δ * B ^ 2 * m))) hhat)
    (hmeas : IsMeasurableSelection f hhat) :
    sampleLaw D m {S | 4 * Real.sqrt (L ^ 2 * B ^ 2 / (δ * m)) * (1 + 8 / (δ * m)) <
        risk f D (hhat S) - optRiskOn Hset f D} ≤ ENNReal.ofReal δ := by sorry

end LearnStability.ConvexSCO
