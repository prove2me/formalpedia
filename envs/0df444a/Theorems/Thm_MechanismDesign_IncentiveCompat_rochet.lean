-- Prove2me | Theorems.Thm_MechanismDesign_IncentiveCompat_rochet
-- name    : MechanismDesign.IncentiveCompat.rochet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:12:17.349961+00:00
-- url     : https://prove2.me/theorems/762cc6c6-f6d6-41e8-8366-401a99c902d4
-- title:
--   Proposition 5.2 -- Rochet's theorem: a decision rule is implementable iff it is cyclically monotone
-- statement:
--   Let $A$ be an arbitrary set of alternatives, $\Theta$ an arbitrary nonempty set of types and $u : A \times \Theta \to \mathbb R$ an arbitrary utility function. A decision rule $q : \Theta \to A$ is implementable (there is a transfer rule $t : \Theta \to \mathbb R$ with $u(q(\theta),\theta) - t(\theta) \ge u(q(\theta'),\theta) - t(\theta')$ for all $\theta, \theta'$) if and only if it is cyclically monotone: for every finite sequence $(\theta^1,\dots,\theta^k)$ of types with $\theta^k = \theta^1$,
--   $$\sum_{\kappa=1}^{k-1}\bigl(u(q(\theta^\kappa),\theta^{\kappa+1}) - u(q(\theta^\kappa),\theta^\kappa)\bigr) \le 0.$$
--
--   This is Rochet's (1987) characterization of implementability. No finiteness, topology or boundedness is assumed on $A$, $\Theta$ or $u$.
--
--   **Formalization Note** Both directions are stated. A sequence of length $k = m + 1$ is a map `Fin (m+1) → Θ` whose first and last entries coincide; `Nonempty Θ` is the standing assumption of §5.2.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.100, Proposition 5.2 (Rochet 1987)

import Mathlib
import Definitions.Def_MechanismDesign_IncentiveCompat_Model

namespace MechanismDesign.IncentiveCompat

/-- Proposition 5.2 (Rochet 1987, p.100): a decision rule is implementable if and only if it is
cyclically monotone. No structure on the set `A` of alternatives or the nonempty set `Θ` of types
is assumed. -/
theorem rochet {A Θ : Type*} [Nonempty Θ] (u : A → Θ → ℝ) (q : Θ → A) :
    Implementable u q ↔ CyclicallyMonotone u q := by sorry

end MechanismDesign.IncentiveCompat
