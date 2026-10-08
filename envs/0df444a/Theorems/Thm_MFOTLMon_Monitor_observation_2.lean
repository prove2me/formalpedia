-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_observation_2
-- name    : MFOTLMon.Monitor.observation_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:37.270489+00:00
-- url     : https://prove2.me/theorems/175aa7eb-0540-49eb-a19f-a63b3c55c208
-- title:
--   Observation (2), proof of Theorem 3.9, pp. 15:16–15:17 — if (α, j, S) ∈ Q_k then (α, j, ∅) ∈ Q_{k′} for some k′ ≥ k
-- statement:
--   Let $\Phi$ be bounded, with each temporal subformula occurring once, and let $Q_k$ be the list $Q$ of $\mathsf M_\Phi$ when it enters its $(k+1)$st loop iteration. For all $k\in\mathbb N$, if $(\alpha,j,S)\in Q_k$, then
--   $$(\alpha,j,\emptyset)\in Q_{k'}\quad\text{for some }k'\ge k.$$
--
--   The page derives it from the update of $Q$ (line 12), the functions $\mathit{waitfor}$ and $\mathit{update}$, and the fact that the time stamps are monotone and make progress; it guarantees that no pending evaluation waits forever.
--
--   **Formalization Note.** Monotonicity and progress of $\bar\tau$ are part of every temporal structure. "Each temporal subformula occurs only once" is the paper's standing assumption of §3.6.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), pp. 15:16–15:17, proof of Theorem 3.9, observation (2)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Algorithm

namespace MFOTLMon.Monitor

/-- Observation (2) in the proof of Theorem 3.9 (pp. 15:16–15:17): for a bounded `Φ` (each temporal
subformula occurring once) and all `k ∈ ℕ`, if `(α, j, S) ∈ Q_k` then `(α, j, ∅) ∈ Q_{k′}` for some
`k′ ≥ k`. (Monotonicity and progress of `τ̄` are fields of `TempStruct`.) -/
theorem observation_2 {S : Signature} (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ)
    (huniq : TemporalSubformulasOnce Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S)), (α, j, W) ∈ (run D Φ k).Q →
      ∃ k', k ≤ k' ∧ (α, j, ([] : List (Formula S))) ∈ (run D Φ k').Q := by sorry

end MFOTLMon.Monitor
