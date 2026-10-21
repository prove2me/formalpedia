-- Prove2me | Theorems.Thm_HyperKCut_Structure_claim_4_1
-- name    : HyperKCut.Structure.claim_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:28.050429+00:00
-- url     : https://prove2.me/theorems/1adc7265-cec7-4822-b04e-e7be275947eb
-- title:
--   Claim 4.1 — a cut-value comparison
-- statement:
--   In the setting of Lemma 4.1, let $(V_1,\ldots,V_k)$ be a maximal minimum $k$-partition, let $S\subseteq V_1$, let $T\subseteq V\setminus V_1$ meet every other part, and let $U$ be a minimum $(S,T)$-terminal source set. Then
--
--   $$d(V_1)\le d(U\cup V_1).$$
--
--   The comparison is a step in the containment argument of Lemma 4.1. The theorem is stated with the lemma's full setting.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 16 (PDF 17), Claim 4.1, in the proof of Lemma 4.1

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Claim 4.1, p. 16, in the setting of Lemma 4.1. -/
theorem claim_4_1 (H : Hypergraph V) (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (P : Fin k → Finset V) (hP : IsMaximalMinKPartition H k P)
    (S T : Finset V) (hS : S ⊆ P 0) (hT : T ⊆ (P 0)ᶜ)
    (hTj : ∀ j : Fin k, j ≠ 0 → (T ∩ P j).Nonempty)
    (U : Finset V) (hU : IsMinTerminalCut H S T U) :
    d H (P 0) ≤ d H (U ∪ P 0) := by sorry

end HyperKCut.Structure
