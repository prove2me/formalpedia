-- Prove2me | Theorems.Thm_ObfEF_Incremental_lemma_3_2
-- name    : ObfEF.Incremental.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:56:53.545559+00:00
-- url     : https://prove2.me/theorems/fb18237c-80fd-43b3-b861-3848801d5ada
-- title:
--   Lemma 3.2 — δ-equivalence via S is an incremental change with support inp(S)
-- statement:
--   Let $D^1$ and $D^2$ be two circuits with the same topology in the gate-list view (same wires, same input wires $l_j,r_j$ of every gate, same output wires; topologically ordered gates, no gate reading an output wire), computing gate functions $f^1_j$ and $f^2_j$, and let $S$ be a set of gates. Then
--   $$D^1,D^2\ \text{are δ-equivalent via } S\iff \text{there is an incremental change } (S,\mathrm{inp}(S),\Gamma)\text{ from } D^1 \text{ to } D^2.$$
--   Here δ-equivalence is Definition 2.3 (gates outside $S$ identical, equal values on $\mathrm{out}(S)$ for every boundary assignment) and an incremental change is Definition 3.1 with support $R=\mathrm{inp}(S)$.
--
--   The lemma shows that incremental changes refine the familiar local equivalence condition: the whole input boundary as support recovers it, and later results bound the support by $3$ instead. It also turns condition 3 of Definition 3.1 into the wording of Theorem 1.2 ("compute the same values on the wires leaving $S_k$").
--
--   Differences from the source:
--   - generalization: circuits over B (gate functions constants, NOT, AND, OR in the gate-list view) → arbitrary gate functions f_j : {0,1}² → {0,1} over a well-formed wiring; reason: neither notion uses the basis; the paper's circuits are the instances whose f_j come from B
--   - encoding: two circuits with the same topology (the same graph up to a renaming of the vertices) → two gate-function maps f₁ f₂ over one Wiring; reason: the renaming is applied first; δ-equivalence and incremental changes compare corresponding gates
--   - encoding: ξ ∈ {0,1}^{inp(S)} → ξ : ℕ → Bool on all wires; reason: the evaluation of S and the describing circuits read ξ only on inp(S)
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 46, Lemma 3.2

import Mathlib
import Definitions.Def_ObfEF_Incremental_GateList
import Definitions.Def_ObfEF_Incremental_DeltaEquiv
import Definitions.Def_ObfEF_Incremental_IncrementalChange

namespace ObfEF.Incremental

/-- Lemma 3.2 (δ-Equivalence as an Incremental Change). Two circuits with the same topology
(gate functions `f₁`, `f₂` over one well-formed wiring `W`) are δ-equivalent via `S` if and only
if there is an incremental change `(S, inp(S), Γ)` from one to the other. -/
theorem lemma_3_2 (W : Wiring) (hW : W.WellFormed) (f₁ f₂ : Fin W.n → Bool → Bool → Bool)
    (S : Finset (Fin W.n)) :
    DeltaEquiv W f₁ f₂ S ↔ ∃ ch : IncrementalChange W f₁ f₂, ch.S = S ∧ ch.R = W.inp S := by sorry

end ObfEF.Incremental
