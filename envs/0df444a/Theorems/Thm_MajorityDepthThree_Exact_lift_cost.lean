-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_lift_cost
-- name    : MajorityDepthThree.Exact.lift_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:31.90684+00:00
-- url     : https://prove2.me/theorems/12fff61a-4788-4d6b-b007-567aed55a124
-- title:
--   Fact 5.10 — cost of a lifted weight
-- statement:
--   Let $\mathcal A$ be a set system on the finite ground set $V$, let $\rho$ be a restriction, and let $f_\rho$ be any nonnegative weight on $\mathcal A_\rho$. For $r=\sqrt{3/2}/2$,
--
--   $$\operatorname{cost}(L_\rho(f_\rho))=r^{|\operatorname{supp}^+(\rho)|}\operatorname{cost}(f_\rho).$$
--
--   Cost on either side uses its own family. No covering feasibility is required. This identity records the exact objective change when adding the positive support back to residual sets.
--
--   Differences from the source:
--   - encoding: A finite ground set V and its subsets → Finite subsets V of a variable type, with finite families of subsets; reason: Every source instance has this representation; all assignments and ambient isolated variables are retained
--   - encoding: Restrictions and the augmented restrictions of Note 5.3 → Disjoint positive and negative supports contained in V, plus optional clauses on unset variables; reason: An empty collection of extra clauses gives ordinary restrictions; residual families and lifted weights use strong consistency, while compatibility remains weaker
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.13, Fact 5.10

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem lift_cost {α : Type} [DecidableEq α] (V : Finset α)
    (A : Family α) (hA : ∀ S ∈ A, S ⊆ V) (ρ : Restriction V)
    (f : Weight α) (hf : ∀ S ∈ residual A ρ, 0 ≤ f S) :
    cost A r (liftWeight ρ f) = r ^ ρ.pos.card * cost (residual A ρ) r f := by sorry

end MajorityDepthThree.Exact
