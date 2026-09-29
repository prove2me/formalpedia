-- Prove2me | Theorems.Thm_NetworkControl_CapacityRegion_lemma_stability_conditions_under_admissibility
-- name    : NetworkControl.CapacityRegion.lemma_stability_conditions_under_admissibility
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T06:20:47.624876+00:00
-- url     : https://prove2.me/theorems/51adf800-fb51-46f7-8619-e479edc7742a
-- title:
--   Lemma 3.6 — stability conditions under admissibility
-- statement:
--   **Lemma 3.6** (p. 26). Consider a queue with an admissible input process $A$ of rate
--   $\lambda$ and an admissible server process $\mathrm{svc}$ of time-average rate $\mu$, whose
--   backlog obeys the book's queueing law (`QueueBacklog`). Then: (a) $\lambda\le\mu$ is a
--   necessary condition for strong stability; (b) $\lambda<\mu$ is a sufficient condition for
--   strong stability. Stated jointly as a conjunction of the two implications, matching the
--   book's own (a)/(b) split.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 26, Lemma 3.6

import Mathlib
import Definitions.Def_NetworkControl_CapacityRegion_QueueBacklog
import Definitions.Def_NetworkControl_CapacityRegion_AdmissibleArrival
import Definitions.Def_NetworkControl_CapacityRegion_AdmissibleService
import Definitions.Def_NetworkControl_CapacityRegion_StronglyStable

namespace NetworkControl.CapacityRegion

open MeasureTheory

/-- Lemma 3.6 (Stability Conditions under Admissibility), p. 26. Consider a queue with backlog
process `QueueBacklog A svc U0` obeying the book's queueing law, fed by an admissible arrival
process `A` of rate `lam` and an admissible server process `svc` of rate `mu`, on a filtered
probability space. Then: (a) `lam ≤ mu` is necessary for strong stability of the expected-backlog
sequence; (b) `lam < mu` is sufficient for it. -/
theorem lemma_stability_conditions_under_admissibility
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ) (lam mu : ℝ)
    (hA : AdmissibleArrival P 𝓕 A lam)
    (hsvc : AdmissibleService P 𝓕 svc mu)
    (hInteg : ∀ t : ℕ, Integrable (QueueBacklog A svc U0 t) P) :
    (StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P) → lam ≤ mu) ∧
      (lam < mu → StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P)) := by sorry

end NetworkControl.CapacityRegion
