-- Prove2me | Theorems.Thm_MarkovEntanglementExact_inducedMatrix_isTransitionMatrix
-- name    : MarkovEntanglementExact.inducedMatrix_isTransitionMatrix
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:25.906662+00:00
-- url     : https://prove2.me/theorems/71fc82a4-160c-47da-a234-37b3a4d7f6ce
-- title:
--   §2, p.7 — $P^\pi_{AB}$ is a transition matrix
-- statement:
--   For a transition kernel $P$ and a policy $\pi$ of a two-agent MDP with feasible action sets, the induced matrix
--   $$P^\pi_{AB}(s',a'\mid s,a)=P(s'\mid s,a)\,\pi(a'\mid s')$$
--   is a transition matrix on joint state-action pairs.
--
--   This connects the MDP of the paper to the matrix-level results of the mission.
--
--   Differences from the source:
--   - generalization: one action set per agent, and |S_A| = |S_B|, |A_A| = |A_B| "for simplicity" → feasible action sets AA s, AB s and unrelated finite state types; reason: footnote 1 restricts the action sets; the constant action set of equal size is the special case AA := fun _ => A
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.7

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsFeasibleKernel
import Definitions.Def_MarkovEntanglementExact_IsFeasiblePolicy
import Definitions.Def_MarkovEntanglementExact_inducedMatrix

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- The matrix `P^π_AB` induced by a kernel and a policy is a transition matrix on joint
state-action pairs.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.7 ("the
transition matrix induced by π"). -/
theorem inducedMatrix_isTransitionMatrix
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    {AA : SA → Type*} {AB : SB → Type*} [∀ s, Fintype (AA s)] [∀ s, Fintype (AB s)]
    (kernel : (s : SA × SB) → AA s.1 × AB s.2 → SA × SB → ℝ)
    (hkernel : IsFeasibleKernel kernel)
    (π : (s : SA × SB) → AA s.1 × AB s.2 → ℝ)
    (hπ : IsFeasiblePolicy π) :
    IsTransitionMatrix (inducedMatrix kernel π) := by sorry

end MarkovEntanglementExact
