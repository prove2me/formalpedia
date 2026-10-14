-- Prove2me | Theorems.Thm_Micromobility_Transient_lemma_H_8
-- name    : Micromobility.Transient.lemma_H_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:20.215799+00:00
-- url     : https://prove2.me/theorems/59cfeb86-cf47-406b-ba20-0a055cf4cf48
-- title:
--   Lemma H.8, p. A-33 — under the triangle inequality there is an optimal policy with π̂*(π̂*(x̆)) = π̂*(x̆)
-- statement:
--   Assume the standing assumptions and that $\hat c_2$ satisfies the triangle inequality of Lemma H.7. Then for every state $\breve x \in \breve X$ there is an optimal stationary policy $\hat\pi^*$ (one that takes, at every state of $\breve X$, an action minimizing the right-hand side of the Bellman equation (3.6)) such that
--   $$\hat\pi^*(\hat\pi^*(\breve x)) = \hat\pi^*(\breve x),$$
--   where the inner $\hat\pi^*(\breve x)$ is an action read as a state (p. A-31).
--
--   Once the system has been rebalanced to an optimal action, staying at that action is again optimal. The proof of Theorem 4.2 uses this to evaluate $\hat V$ at an action-state.
--
--   **Formalization Note.** The triangle-inequality hypothesis is the paper's; it is discharged by Lemma H.7.
-- source:
--   Akturk, Candogan, Gupta, Managing Resources for Shared Micromobility: Approximate Optimality in Large-Scale Systems, SSRN 4155841 (version of 2024-05-22), p. A-33, Lemma H.8 (cited from Akturk (2022), Lemma 2.2)

import Mathlib
import Definitions.Def_Micromobility_Transient_Setting

namespace Micromobility.Transient
theorem lemma_H_8 {ê : ℕ} (M : Model ê) (hM : M.Standing) (htri : M.TriangleIneq)
    (x : State ê) (hx : M.InX x) :
    ∃ π : State ê → Action ê, M.IsOptimalPolicy π ∧ π (toState (π x)) = π x := by sorry
end Micromobility.Transient
