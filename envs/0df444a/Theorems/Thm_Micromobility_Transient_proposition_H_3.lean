-- Prove2me | Theorems.Thm_Micromobility_Transient_proposition_H_3
-- name    : Micromobility.Transient.proposition_H_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:27.804215+00:00
-- url     : https://prove2.me/theorems/1baf4c29-bd91-429f-9708-83193d659f6b
-- title:
--   Proposition H.3, p. A-28 — for q = 0 the dynamic program (3.6) has a fixed point (Definition H.1)
-- statement:
--   Under the standing assumptions, if $q = 0$ (every returned unit is depleted), the dynamic program (3.6) has the fixed point property: there are a state $\breve x^f \in \breve X$ and an action $\hat a^f$ optimal at $\breve x^f$ such that taking $\hat a^f$ leads back to $\breve x^f$:
--   $$\breve x'(\hat a^f) = \breve x^f.$$
--
--   For $q = 0$ the transitions (F.1)–(F.5) are affine in the action, which is what makes a steady state exist. The fixed point gives Theorem 4.2's sharper bound $C\gamma^T$ in this case.
--
--   **Formalization Note.** "Optimal action" means a minimizer of the right-hand side of (3.6) over $\hat A$ (Definition H.1, p. A-28).
-- source:
--   Akturk, Candogan, Gupta, Managing Resources for Shared Micromobility: Approximate Optimality in Large-Scale Systems, SSRN 4155841 (version of 2024-05-22), p. A-28, Proposition H.3 and Definition H.1

import Mathlib
import Definitions.Def_Micromobility_Transient_Setting

namespace Micromobility.Transient
theorem proposition_H_3 {ê : ℕ} (M : Model ê) (hM : M.Standing) (hq : M.q = 0) : ∃ xf af, M.IsFixedPoint xf af := by sorry
end Micromobility.Transient
