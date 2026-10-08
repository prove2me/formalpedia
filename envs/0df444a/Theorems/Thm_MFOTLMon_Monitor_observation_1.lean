-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_observation_1
-- name    : MFOTLMon.Monitor.observation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:30.438211+00:00
-- url     : https://prove2.me/theorems/f08e6853-20e5-4b72-bb8f-fab22a0d74f8
-- title:
--   Observation (1), proof of Theorem 3.9, p. 15:16 — for all k ∈ ℕ, (α, k, waitfor(α)) ∈ Q_k
-- statement:
--   Let $Q_k$ be the list $Q$ of the monitor $\mathsf M_\Phi$ when it enters its $(k+1)$st loop iteration. For every temporal subformula $\alpha$ of $\Phi$ and every $k\in\mathbb N$,
--   $$(\alpha,k,\mathit{waitfor}(\alpha))\in Q_k.$$
--
--   Together with Observation (2) this shows that the auxiliary relations of every temporal subformula are eventually built at every time point.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), p. 15:16, proof of Theorem 3.9, observation (1)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Algorithm

namespace MFOTLMon.Monitor

/-- Observation (1) in the proof of Theorem 3.9 (p. 15:16): for every temporal subformula `α` of `Φ`
and all `k ∈ ℕ`, `(α, k, waitfor(α)) ∈ Q_k`. -/
theorem observation_1 {S : Signature} (D : TempStruct S) (Φ : Formula S) :
    ∀ α ∈ tempSubs Φ, ∀ k : ℕ, (α, k, waitfor α) ∈ (run D Φ k).Q := by sorry

end MFOTLMon.Monitor
