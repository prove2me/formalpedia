-- Prove2me | Theorems.Thm_MITMSynthesis_depthOneSet_subset_unitary
-- name    : MITMSynthesis.depthOneSet_subset_unitary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:05:15.578688+00:00
-- url     : https://prove2.me/theorems/4f97d179-4af1-4766-b21c-f362f6b1f0e8
-- title:
--   Every element of $V_{n,\mathcal G}$ is unitary
-- statement:
--   Let $\mathcal G$ be a set of gates and $n \in \mathbb N$. Every element of $V_{n,\mathcal G}$, the set of unitaries of depth-one $n$-qubit circuits over $\mathcal G$, is a unitary matrix:
--
--   $$
--   V_{n,\mathcal G} \subseteq U(2^n).
--   $$
--
--   The paper introduces $V_{n,\mathcal G}$ as "the set of all unitaries corresponding to depth one n-qubit circuits"; this statement records that a gate on some qubits tensored with the identity, and a product of such, is unitary. It is used whenever a circuit $V$ is undone by $V^\dagger$.
--
--   Differences from the source: none.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §2, p. 4 (V_{n,G}, "the set of all unitaries corresponding to depth one n-qubit circuits over the instruction set G")

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S

namespace MITMSynthesis

/-- **Every element of `V_{n,G}` is unitary.** Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3,
§2, p. 4: `V_{n,G}` is "the set of all unitaries corresponding to depth one n-qubit circuits over
the instruction set G". Each gate of `G` is unitary, its placement on qubits (tensored with the
identity) is unitary, and a layer is a product of such placements. -/
theorem depthOneSet_subset_unitary (n : ℕ) (G : Set Gate) :
    depthOneSet n G ⊆ (Matrix.unitaryGroup (Q n) ℂ : Set (Matrix (Q n) (Q n) ℂ)) := by sorry

end MITMSynthesis
