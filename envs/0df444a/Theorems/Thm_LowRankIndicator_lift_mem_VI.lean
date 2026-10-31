-- Prove2me | Theorems.Thm_LowRankIndicator_lift_mem_VI
-- name    : LowRankIndicator.lift_mem_VI
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:48.444459+00:00
-- url     : https://prove2.me/theorems/b63c7bf3-33da-4bdf-ba26-d2af84435edb
-- title:
--   Proof of Theorem 1, p.8 — $(\bar t+c^\top(x^*-\bar x),x^*,\bar z)\in V(\operatorname{supp}(x^*))$
-- statement:
--   Let $(\bar t,\bar x,\bar z)\in Q$ and let $x^*$ be feasible for the linear program (7). Put $t^*=\bar t+c^\top(x^*-\bar x)$. Then
--
--   $$(t^*,x^*,\bar z)\in V(\operatorname{supp}(x^*)).$$
--
--   Since $Ax^*=A\bar x$, the nonlinear term of $f$ does not change between $\bar x$ and $x^*$, so moving the continuous part of a point of $Q$ inside (7) keeps it in a piece of the decomposition.
--
--   Differences from the source:
--   - generalization: x∗ optimal for (7), g proper closed convex → x∗ feasible for (7), arbitrary g : ℝᵏ → `EReal`; reason: optimality and these properties are not needed, and the statement specializes to the paper's x∗ and g
--   - encoding: real and extended values, I = supp(x∗) → `EReal`, `supp xstar : Finset (Fin n)`; reason: Lean conventions, same instances
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, proof of Theorem 1, p.8, "t∗ def= t̄ + c⊤(x∗ − x̄)" and "Setting I = supp(x∗)".

import Mathlib
import Definitions.Def_LowRankIndicator_Sets
import Definitions.Def_LowRankIndicator_FeasibleSet7

open scoped Matrix

namespace LowRankIndicator

/-- Han & Gómez, arXiv:2110.14884v2, proof of Theorem 1, p.8: for `(t̄, x̄, z̄) ∈ Q` and `x∗` feasible
for (7), the point `(t∗, x∗, z̄)` with `t∗ = t̄ + c⊤(x∗ − x̄)` lies in `V(supp(x∗))`.

**Formalization Note.** `g` is an arbitrary `EReal`-valued function. Optimality of `x∗` is not
needed. The paper's chain `t∗ ≥ f(x∗)` is part of `V(supp(x∗))`. -/
theorem lift_mem_VI {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin n → ℝ) (Iplus : Set (Fin n)) {tbar : ℝ} {xbar zbar xstar : Fin n → ℝ}
    (hbar : (tbar, xbar, zbar) ∈ Q g A c Iplus) (hstar : xstar ∈ feas7 A xbar) :
    (tbar + c ⬝ᵥ (xstar - xbar), xstar, zbar) ∈ VI g A c Iplus (supp xstar) := by sorry

end LowRankIndicator
