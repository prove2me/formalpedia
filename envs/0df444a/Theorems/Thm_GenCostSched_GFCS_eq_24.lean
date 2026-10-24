-- Prove2me | Theorems.Thm_GenCostSched_GFCS_eq_24
-- name    : GenCostSched.GFCS.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:39.169284+00:00
-- url     : https://prove2.me/theorems/ddfa39f9-f21d-4567-ab88-9fe2a8f7733b
-- title:
--   (24), proof of Theorem 3, pp. 21–22 — ∫_{r_n}^∞ β̂_t dt = Σ_ℓ ∫_{I_ℓ} (t − r_n) g′_ℓ(t) dt
-- statement:
--   Let GFCS(s) be an identical-release instance (jobs $A$ released no later than $s$, standing assumptions of §II). Let $x$ be an integral schedule of it: rates in $\{0,1\}$, zero before $s$, each job processed exactly its length, finished in finite time. Let $I_\ell=\{t: x_\ell(t)=1\}$ be the times at which job $\ell$ is processed, and $\hat\beta_t=\sum_\ell\int_{(t,\infty)}g'_\ell x_\ell$ as in (20). Then
--   $$\int_s^\infty\hat\beta_t\,dt\;=\;\sum_\ell\int_{I_\ell}(t-s)\,g'_\ell(t)\,dt .$$
--
--   With $s=r_n$, applied to the schedules before and after the arrival of job $n$, this yields the first identity (24) of the proof of Theorem 3. It expresses the β̂-part of the dual objective through the cost derivatives over the processing intervals.
--
--   **Formalization Note.** The right side is written as $\sum_\ell\int_{[s,\infty)}(t-s)g'_\ell(t)x_\ell(t)\,dt$.
--
--   Differences from the source:
--
--   - generalization: I_ℓ (resp. I′_ℓ) the processing intervals of the optimal schedule followed by Algorithm 2 → every integral schedule x of GFCS(s); reason: the identity holds for every such schedule; the optimal ones are special cases
--   - encoding: β̂_t = Σ_ℓ Σ_d [g_ℓ(C_ℓ^{2d}) − g_ℓ(C_ℓ^{2d−1})] over the processing intervals after t → β̂_t = Σ_ℓ ∫_{(t,∞)} g′_ℓ(τ) x_ℓ(τ) dτ (betaHat); reason: equal by the fundamental theorem of calculus on each interval, as in (23), p. 21; the integral form is defined for every measurable schedule
--   - encoding: the derivative g′_j of g_j on [r_j, ∞) → a given function g' j tied to g j by HasDerivWithinAt (g j) (g' j t) (Ici (r j)) t for t ≥ r_j (JobStanding); reason: g_j is defined and differentiable only on [r_j, ∞) (p. 5), so its derivative there is the within-derivative; supplying it as data changes no instance
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, pp. 21–22, proof of Theorem 3, the chain after (23) and the sentence before (24)

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-- (24) (proof of Theorem 3, pp. 21–22): for an integral schedule `x` of GFCS(s),
`∫_s^∞ β̂_t dt = ∑_ℓ ∫_{I_ℓ} (t − s) g′_ℓ(t) dt`, where `I_ℓ` is the set of times at which `x`
processes job `ℓ`. -/
theorem eq_24 {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s)
    (x : Fin m → ℝ → ℝ) (hx : IsOffIntSched s A ρ x) :
    ∫ t in Ici s, betaHat I.g' x t = ∑ ℓ, ∫ t in Ici s, (t - s) * I.g' ℓ t * x ℓ t := by sorry

end GenCostSched.GFCS
