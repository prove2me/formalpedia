-- Prove2me | Theorems.Thm_MITMSynthesis_star_mem_depthOneSet
-- name    : MITMSynthesis.star_mem_depthOneSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:05:54.973801+00:00
-- url     : https://prove2.me/theorems/4e429c5b-30e6-45fb-8516-b19179b66273
-- title:
--   $V_{n,\mathcal G}$ is closed under adjoints
-- statement:
--   Let $\mathcal G$ be an instruction set, that is, a set of gates containing the inverse of each of its gates. Then for every $n$,
--
--   $$
--   M \in V_{n,\mathcal G} \implies M^\dagger \in V_{n,\mathcal G}.
--   $$
--
--   This is the step of the proof of Lemma 1 showing that the adjoint of a depth-$i$ circuit is again a depth-$i$ circuit; it is why the inverse-closure of the instruction set is required.
--
--   Differences from the source: none.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, proof of Lemma 1, pp. 5–6 ("As G is closed under inversion, U_1†, U_2†, ..., U_i† ∈ V_{n,G}")

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S

namespace MITMSynthesis

/-- **`V_{n,G}` is closed under `†`.** Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3, proof of
Lemma 1, pp. 5–6: "As G is closed under inversion, U₁†, U₂†, …, U_i† ∈ V_{n,G}". If the instruction
set `G` contains the inverse of each of its gates, the adjoint of every depth-one unitary over `G`
is again a depth-one unitary over `G`. -/
theorem star_mem_depthOneSet {n : ℕ} {G : Set Gate} (hG : IsInstructionSet G)
    {M : Matrix (Q n) (Q n) ℂ} (hM : M ∈ depthOneSet n G) : star M ∈ depthOneSet n G := by sorry

end MITMSynthesis
