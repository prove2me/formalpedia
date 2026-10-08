-- Prove2me | Theorems.Thm_NestedLogitVariants_PartialCompetitive_ineq_28
-- name    : NestedLogitVariants.PartialCompetitive.ineq_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:08:09.909585+00:00
-- url     : https://prove2.me/theorems/4e6fe852-e3cf-40ac-bb14-eea77c0b606f
-- title:
--   (28), A.3 Case 1, pp. 45–46 — if ẑ_i(ϵ) has a fractional component, 2ŷ_i ≥ (v_i0+ϵ)^γ_i [K_i(ϵ)/(v_i0+ϵ) − 2x̂]
-- statement:
--   Consider a nested logit instance with $\gamma_i \le 1$ for every nest and at least one product per nest, and let $(\hat x, \hat y)$ be an optimal solution of the linear program (4) over the candidate collections $\{\hat S_i(\epsilon_i) : \epsilon_i \in [0,\infty]\} \cup \{\{j\} : j \in N\}$. Fix a nest $i$ and a capacity $\epsilon \ge 0$, and suppose that the greedy solution $\hat z_i(\epsilon)$ of the continuous knapsack problem (11) has a fractional component $k$, $0 < \hat z_{ik}(\epsilon) < 1$. Then
--
--   $$2\hat y_i \ge (v_{i0} + \epsilon)^{\gamma_i}\Big[\frac{K_i(\epsilon)}{v_{i0} + \epsilon} - 2\hat x\Big].$$
--
--   This is Case 1 of the proof of Theorem 10: the constraints of (4) for $\hat S_i(\epsilon)$ and for the singleton $\{k\}$ together dominate the continuous knapsack value, hence the knapsack value.
--
--   **Formalization Note** The page states (28) at a maximizer $\hat\epsilon_i$ of the right side of (10) at $x = 2\hat x$; the argument applies to every capacity $\epsilon \ge 0$, and that is the form stated here, which is what feasibility in (10) requires. The page writes the right side as $K_i(\epsilon)/(v_{i0}+\epsilon)^{1-\gamma_i} - (v_{i0}+\epsilon)^{\gamma_i}\, 2\hat x$; for $v_{i0} + \epsilon > 0$ the two forms are equal. The hypothesis $n \ge 1$ is the paper's nonempty $N$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 45–46, Appendix A.3, Case 1, displays (26)–(28)

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

namespace NestedLogitVariants.PartialCompetitive

/-- Inequality (28), A.3 Case 1, pp. 45–46: if `ẑ_i(ε)` has a fractional component `k`, then
`2 ŷ_i ≥ (v_{i0} + ε)^{γ_i} [K_i(ε)/(v_{i0} + ε) − 2 x̂]`. Stated for every `ε ≥ 0`. -/
theorem ineq_28 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hn : 0 < n)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidates I) xh yh)
    (i : ι) (ε : ℝ) (hε : 0 ≤ ε) (k : Fin n) (hk : zhat I i ε k ∈ Set.Ioo (0 : ℝ) 1) :
    (I.vnp i + ε) ^ I.γ i * (Kval I i ε / (I.vnp i + ε) - 2 * xh) ≤ 2 * yh i := by sorry

end NestedLogitVariants.PartialCompetitive
