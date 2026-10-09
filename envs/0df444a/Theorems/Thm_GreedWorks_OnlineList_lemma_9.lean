-- Prove2me | Theorems.Thm_GreedWorks_OnlineList_lemma_9
-- name    : GreedWorks.OnlineList.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:56.409889+00:00
-- url     : https://prove2.me/theorems/24b20e7e-4694-4fe9-a2a7-e29f070f369a
-- title:
--   Lemma 9, p. 21 — expected completion time from processing-slot probabilities
-- statement:
--   Consider one job with integer start time $T$ and strictly positive integer processing time $P$. Assume $T$ and $P$ are measurable and independent, $T$ has finite mean, and $P$ has finite second moment. Write $\mu=\mathbb E[P]$, $\mathrm{CV}[P]^2=\operatorname{Var}(P)/\mu^2$, and $y_s=\mathbb P(T\le s<T+P)$, the probability of occupying slot $s$. Then the series has sum
--
--   $$\mathbb E[T+P]=\sum_{s\ge0}\left[\frac{y_s}{\mu}\left(s+\frac12\right)+\frac{1-\mathrm{CV}[P]^2}{2}\,y_s\right].$$
--
--   This supplies the completion-time formula (4) of the stochastic LP. **Formalization Note** Independence is the single-job content of the paper's nonanticipation explanation: the start decision cannot depend on the job's own processing time.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 21, Appendix A, Lemma 9

import Mathlib

namespace GreedWorks.OnlineList

open MeasureTheory ProbabilityTheory

/-- Gupta et al., Lemma 9, p. 21: formula (4) for the expected completion
time of one nonanticipatorily started job.  Independence states that the start
decision does not depend on this job's own processing time. -/
theorem lemma_9 {Ω : Type*} [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (T P : Ω → ℕ) (hT : Measurable T) (hP : Measurable P)
    (hPpos : ∀ ω, 1 ≤ P ω)
    (hP2 : MemLp (fun ω => (P ω : ℝ)) 2 Pr)
    (hTint : Integrable (fun ω => (T ω : ℝ)) Pr)
    (hIndep : IndepFun T P Pr) :
    let μ : ℝ := ∫ ω, (P ω : ℝ) ∂Pr
    let cv2 : ℝ := variance (fun ω => (P ω : ℝ)) Pr / μ ^ 2
    let y : ℕ → ℝ := fun s => (Pr {ω | T ω ≤ s ∧ s < T ω + P ω}).toReal
    HasSum (fun s : ℕ =>
      y s / μ * ((s : ℝ) + 1 / 2) + (1 - cv2) / 2 * y s)
      (∫ ω, ((T ω + P ω : ℕ) : ℝ) ∂Pr) := by sorry

end GreedWorks.OnlineList
