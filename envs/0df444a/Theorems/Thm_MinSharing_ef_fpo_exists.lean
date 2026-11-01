-- Prove2me | Theorems.Thm_MinSharing_ef_fpo_exists
-- name    : MinSharing.ef_fpo_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:10.468585+00:00
-- url     : https://prove2.me/theorems/22e18ab4-472d-4f12-8a67-3c399067fd29
-- title:
--   p.11, citing Bogomolnaia et al. (2017) — envy-free fPO allocations exist for mixed problems
-- statement:
--   For every number $n\ge1$ of agents, every number $m$ of objects and every valuation matrix $v\in\mathbb R^{n\times m}$ (goods, bads and neutral objects mixed, no sign restriction) there is an allocation $z$ that is fractionally Pareto-optimal and envy-free:
--   $$u_i(z_i)\ge u_i(z_j)\quad\text{for all agents } i,j .$$
--
--   This is the existence result of Bogomolnaia, Moulin, Sandomirskiy and Yanovskaya (2017), cited by the paper in the proof of Corollary 2.6; the allocation can be taken to be a competitive equilibrium with equal incomes. It guarantees that the envy-free version of the sharing-minimization problem of Theorem 3.6(a) is feasible.
--
--   Differences from the source:
--   - encoding: any instance (n agents) → n ≥ 1; reason: with no agents no object can be allocated, so the statement is about n ≥ 1
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, proof of Corollary 2.6, p.11 ("The existence of envy-free fPO allocations for mixed problems was proved by Bogomolnaia et al. (2017)"); A. Bogomolnaia, H. Moulin, F. Sandomirskiy, E. Yanovskaya, Competitive division of a mixed manna, Econometrica 85(6), 2017

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_MinSharing_Setting

set_option autoImplicit false

namespace MinSharing

open CompetitiveChores.RichFamily

/-- **Existence of envy-free fPO allocations for mixed problems** (Bogomolnaia, Moulin,
Sandomirskiy, Yanovskaya 2017, cited in the proof of Corollary 2.6 of Sandomirskiy, Segal-Halevi,
arXiv:1908.01669v3, p.11): "The existence of envy-free fPO allocations for mixed problems was
proved by Bogomolnaia et al. (2017)." For every instance with `n ≥ 1` agents, `m` objects and a
valuation matrix `v` of arbitrary signs there is a fractionally Pareto-optimal envy-free
allocation.

**Formalization Note** `n ≥ 1` because with no agents no object can be allocated. No sign
condition on `v`. -/
theorem ef_fpo_exists (n m : ℕ) (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) :
    ∃ z, IsParetoOptimal v z ∧ IsEF v z := by sorry

end MinSharing
