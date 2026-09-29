-- Prove2me | Theorems.Thm_LearnStability_ConvexSCO_theorem2_expectation
-- name    : LearnStability.ConvexSCO.theorem2_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:16:48.345023+00:00
-- url     : https://prove2.me/theorems/67509d22-7201-483e-b467-204c62ba480a
-- title:
--   Strongly convex ERM in expectation: $\mathbb E[F(\hat h_S)-F^*]\le 4L^2/(\lambda m)$
-- statement:
--   Consider a stochastic convex optimization problem on $\mathcal H$ (closed, convex, bounded, in a Hilbert space) whose objective is, for every $z$, $\lambda$-strongly convex ($\lambda>0$) and $L$-Lipschitz in $h\in\mathcal H$, with $|f|\le C$. Let $\hat h_S$ be an empirical minimizer of $F_S$ over $\mathcal H$, chosen measurably in the sample. Then for every distribution $D$ and every $m\ge1$,
--   $$\mathbb E_{S\sim D^m}\big[F(\hat h_S)-F^*\big]\ \le\ \frac{4L^2}{\lambda m},\qquad F^*=\inf_{h\in\mathcal H}F(h).$$
--
--   This is the in-expectation form of Theorem 2; the high-probability form follows from it because $F(\hat h_S)-F^*\ge0$.
--
--   **Formalization Note** The empirical minimizer is a selection $S\mapsto\hat h_S$; the statement holds for every such selection with $(S,z)\mapsto f(\hat h_S;z)$ jointly measurable (series convention, not in the paper).
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2645, proof of Theorem 2, last display

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting
import Definitions.Def_LearnStability_ConvexSCO_Problem

open MeasureTheory

namespace LearnStability.ConvexSCO

/-- Proof of Theorem 2, last display (p. 2645): for a stochastic convex optimization problem
whose objective is `λ`-strongly convex (`λ > 0`) and `L`-Lipschitz in `h ∈ H`, every measurable
selection of empirical minimizers `ĥ_S` over `H` satisfies
`E_{S∼D^m}[F(ĥ_S) − F*] ≤ 4L²/(λm)` for every distribution `D` and every `m ≥ 1`. -/
theorem theorem2_expectation {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {f : E → Z → ℝ} {L C lam : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hlam : 0 < lam)
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z))
    (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m)
    (hhat : (Fin m → Z) → E) (hmin : IsEmpMinimizerOn Hset f hhat)
    (hmeas : IsMeasurableSelection f hhat) :
    ∫ S, (risk f D (hhat S) - optRiskOn Hset f D) ∂(sampleLaw D m) ≤
      4 * L ^ 2 / (lam * m) := by sorry

end LearnStability.ConvexSCO
