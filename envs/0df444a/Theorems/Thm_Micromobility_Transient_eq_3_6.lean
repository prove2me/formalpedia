-- Prove2me | Theorems.Thm_Micromobility_Transient_eq_3_6
-- name    : Micromobility.Transient.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:20.763218+00:00
-- url     : https://prove2.me/theorems/1b439cea-6504-4d61-9135-28523b0ca235
-- title:
--   (3.6), p. 25 — V̂ satisfies the Bellman equation on X̆ and the minimum over Â is attained
-- statement:
--   Consider the compact mean-field model under its standing assumptions, with value function $\hat V$ (the infimum of the discounted cost over action sequences in $\hat A$). For every state $\breve x \in \breve X$ there is an action $\hat a \in \hat A$ that is optimal at $\breve x$ and attains the Bellman equation:
--   $$\hat V(\breve x) = \min_{\hat a \in \hat A}\ \hat c_2(\breve x, \hat a) + \hat N(\hat a) + \gamma\,\hat V(\breve x'(\hat a)),$$
--   where $\breve x'(\hat a)$ is the next state given by (F.1)–(F.5).
--
--   This is the dynamic-programming principle for the deterministic mean-field model, together with the attainment of the minimum over the action set. It is what lets the paper speak of optimal actions and optimal policies in Appendix H.
--
--   **Formalization Note.** The paper introduces $\hat V$ on $\breve X$ "through the fixed point of the Bellman recursion"; here $\hat V$ is defined as the infimum over action sequences (p. 18, Proposition F.3) and (3.6) is the statement to prove. "Optimal at $\breve x$" means minimizing the right-hand side over $\hat A$.
-- source:
--   Akturk, Candogan, Gupta, Managing Resources for Shared Micromobility: Approximate Optimality in Large-Scale Systems, SSRN 4155841 (version of 2024-05-22), p. 25, §3.4, (3.6)

import Mathlib
import Definitions.Def_Micromobility_Transient_Setting

namespace Micromobility.Transient
theorem eq_3_6 {ê : ℕ} (M : Model ê) (hM : M.Standing) (x : State ê) (hx : M.InX x) :
    ∃ a, M.IsOptimalAction x a ∧ M.Vhat x = M.c2 x a + M.Nhat a + M.γ * M.Vhat (M.next a) := by sorry
end Micromobility.Transient
