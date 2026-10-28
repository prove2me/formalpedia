-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_25
-- name    : NQueensComp.NPC.lemma_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:41.40219+00:00
-- url     : https://prove2.me/theorems/08452980-4a91-4eb9-9e51-b904fe41dd08
-- title:
--   Lemma 25 — Q solves G iff Q + (δ, 0) solves G ⊕ δ
-- statement:
--   For an instance $G=\langle n,C,R,D^-,\{\}\rangle$ of Problem 4 with no excluded sum-diagonals and an integer $\delta\ge0$, Definition 24 sets $G\oplus\delta=\langle n+\delta,\{c+\delta\mid c\in C\},R,\{d+\delta\mid d\in D^-\},\{\}\rangle$.
--
--   **Lemma 25.** A set of queens $Q$ is a solution to $G$ iff $Q+(\delta,0)$ is a solution to $G\oplus\delta$:
--   $$Q \text{ solves } G\iff Q+(\delta,0)\text{ solves } G\oplus\delta.$$
--
--   This lets every variable gadget be a shifted copy of the single gadget $G^0$, with its two solutions shifted along.
--
--   **Formalization Note** The statement is made for every quadruple $\langle n,C,R,D^-\rangle$ with $D^+=\{\}$, without requiring it to be a valid instance of Problem 4.
--
--   Differences from the source:
--   - generalization: G an instance of Problem 4 with D⁺ = {} (a gadget) → any G with D⁺ = {}, valid or not; reason: the proof uses only that translation by (δ, 0) preserves attacks and shifts columns and difference-diagonals by δ; every source instance is covered
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 831, Definition 24 and Lemma 25

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 25, p. 831: for a gadget `G = ⟨n, C, R, D⁻, {}⟩` and `δ ≥ 0`, a set of queens `Q` is a
solution to `G` iff `Q + (δ, 0)` is a solution to `G ⊕ δ`. -/
theorem lemma_25 (G : Inst4) (hG : G.Dp = ∅) (δ : ℕ) (Q : Finset Queen) :
    G.IsSol Q ↔ (G.shift δ).IsSol (shiftSet Q (δ, 0)) := by sorry

end NQueensComp.NPC
