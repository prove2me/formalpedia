-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_observation_3
-- name    : MFOTLMon.Monitor.observation_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:55.335164+00:00
-- url     : https://prove2.me/theorems/1f293a55-793c-4a20-b85c-f92e7fae485b
-- title:
--   Observation (3), proof of Theorem 3.9, p. 15:17 — if (α, j, S) ∈ Q_k then j ≥ i_k
-- statement:
--   Let $Q_k$ and $i_k$ be the list $Q$ and the counter $i$ of $\mathsf M_\Phi$ when it enters its $(k+1)$st loop iteration, $\Phi$ having each temporal subformula occur once. For all $k\in\mathbb N$, if $(\alpha,j,S)\in Q_k$, then
--   $$j\ge i_k.$$
--
--   It is the reason no relation the monitor still needs has been discarded: discarding only removes time points before $i_k-1$.
--
--   **Formalization Note.** "Each temporal subformula occurs only once" is the paper's standing assumption of §3.6.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), p. 15:17, proof of Theorem 3.9, observation (3)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Algorithm

namespace MFOTLMon.Monitor

/-- Observation (3) in the proof of Theorem 3.9 (p. 15:17): for all `k ∈ ℕ`, if `(α, j, S) ∈ Q_k`
then `j ≥ i_k` (each temporal subformula of `Φ` occurring once). -/
theorem observation_3 {S : Signature} (D : TempStruct S) (Φ : Formula S)
    (huniq : TemporalSubformulasOnce Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S)), (α, j, W) ∈ (run D Φ k).Q →
      (run D Φ k).i ≤ j := by sorry

end MFOTLMon.Monitor
