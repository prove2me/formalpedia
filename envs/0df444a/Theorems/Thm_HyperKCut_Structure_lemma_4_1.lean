-- Prove2me | Theorems.Thm_HyperKCut_Structure_lemma_4_1
-- name    : HyperKCut.Structure.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:20.733013+00:00
-- url     : https://prove2.me/theorems/b101d0e9-47e7-48d8-b100-eda1f7330d46
-- title:
--   Lemma 4.1 — minimum terminal cuts stay inside the first part
-- statement:
--   Let $(V_1,\ldots,V_k)$ be a maximal minimum $k$-partition of a finite hypergraph, where $k\ge2$. Let $S\subseteq V_1$ and $T\subseteq V\setminus V_1$ meet every part $V_j$ for $j\ge2$. If $U$ is the source set of a minimum $(S,T)$-terminal cut, then
--
--   $$U\subseteq V_1.$$
--
--   This containment allows the source-maximal cuts used in Theorem 1.2 to remain in the chosen first part.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 15 (PDF 16), Lemma 4.1

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lemma 4.1, p. 15: every minimum terminal source set lies inside the first part. -/
theorem lemma_4_1 (H : Hypergraph V) (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (P : Fin k → Finset V) (hP : IsMaximalMinKPartition H k P)
    (S T : Finset V) (hS : S ⊆ P 0) (hT : T ⊆ (P 0)ᶜ)
    (hTj : ∀ j : Fin k, j ≠ 0 → (T ∩ P j).Nonempty)
    (U : Finset V) (hU : IsMinTerminalCut H S T U) :
    U ⊆ P 0 := by sorry

end HyperKCut.Structure
