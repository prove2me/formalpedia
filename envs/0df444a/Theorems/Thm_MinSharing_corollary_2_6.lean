-- Prove2me | Theorems.Thm_MinSharing_corollary_2_6
-- name    : MinSharing.corollary_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:48.636824+00:00
-- url     : https://prove2.me/theorems/09344efc-5b01-468f-9ac0-306fcca7868b
-- title:
--   Corollary 2.6 (first sentence) — an fPO envy-free (hence proportional) allocation with at most $n-1$ sharings exists
-- statement:
--   In any instance with $n\ge1$ agents, $m$ objects and a real valuation matrix $v$ of arbitrary signs, there is an allocation $z$ that is fractionally Pareto-optimal, envy-free and proportional, and has
--   $$\#\mathrm{shar}_z\le n-1 .$$
--
--   This is the first sentence of Corollary 2.6; the second sentence (strongly polynomial computation in special cases) is a separate claim and is not part of this item. The corollary shows that the feasible set of the envy-free sharing-minimization problem of Theorem 3.6(a) is nonempty and contains allocations with few sharings.
--
--   Differences from the source:
--   - encoding: "(and thus proportional)" → the explicit conjunct IsProp v z; reason: the parenthetical is part of the conclusion
--   - encoding: any instance with n agents → n ≥ 1; reason: with no agents no object can be allocated
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Corollary 2.6, first sentence, p.11

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_MinSharing_Setting

set_option autoImplicit false

namespace MinSharing

open CompetitiveChores.RichFamily

/-- **Corollary 2.6, first sentence** (Sandomirskiy, Segal-Halevi, arXiv:1908.01669v3, p.11).
In any instance with `n` agents there exists a fractionally Pareto-optimal, envy-free (and thus
proportional) division with at most `n − 1` sharings.

**Formalization Note** `n ≥ 1` agents, any `m`, values of any sign. "(and thus proportional)" is
stated as the conjunct `IsProp`. The second sentence of the corollary (strongly-polynomial
computation in special cases) is a separate claim and is not part of this item. -/
theorem corollary_2_6 (n m : ℕ) (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) :
    ∃ z, IsParetoOptimal v z ∧ IsEF v z ∧ IsProp v z ∧ numSharings z ≤ n - 1 := by sorry

end MinSharing
