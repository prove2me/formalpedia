-- Prove2me | Theorems.Thm_NestedLogitVariants_PartialCompetitive_ineq_29
-- name    : NestedLogitVariants.PartialCompetitive.ineq_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:08:20.411667+00:00
-- url     : https://prove2.me/theorems/cfbc0546-3143-44b1-9ec5-fbb71e4baf24
-- title:
--   (29), A.3 Case 2, p. 46 — if ẑ_i(ϵ) has no fractional component, 2ŷ_i ≥ (v_i0+ϵ)^γ_i [K_i(ϵ)/(v_i0+ϵ) − 2x̂]
-- statement:
--   Consider a nested logit instance with $\gamma_i \le 1$ for every nest and at least one product per nest, and let $(\hat x, \hat y)$ be an optimal solution of the linear program (4) over the candidate collections $\{\hat S_i(\epsilon_i) : \epsilon_i \in [0,\infty]\} \cup \{\{j\} : j \in N\}$. Fix a nest $i$ and a capacity $\epsilon \ge 0$, and suppose that no component of the greedy solution $\hat z_i(\epsilon)$ of (11) lies strictly between $0$ and $1$. Then
--
--   $$2\hat y_i \ge (v_{i0} + \epsilon)^{\gamma_i}\Big[\frac{K_i(\epsilon)}{v_{i0} + \epsilon} - 2\hat x\Big].$$
--
--   This is Case 2 of the proof of Theorem 10: here the constraint of (4) for $\hat S_i(\epsilon)$ alone dominates the knapsack value.
--
--   **Formalization Note** As for (28), the page states (29) at a maximizer $\hat\epsilon_i$; the statement here holds for every capacity $\epsilon \ge 0$, and the page's form $K_i(\epsilon)/(v_{i0}+\epsilon)^{1-\gamma_i} - (v_{i0}+\epsilon)^{\gamma_i}\,2\hat x$ equals the bracket form for $v_{i0} + \epsilon > 0$. The hypothesis $n \ge 1$ is the paper's nonempty $N$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 46, Appendix A.3, Case 2, display (29)

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

namespace NestedLogitVariants.PartialCompetitive

/-- Inequality (29), A.3 Case 2, p. 46: if `ẑ_i(ε)` has no fractional component, then
`2 ŷ_i ≥ (v_{i0} + ε)^{γ_i} [K_i(ε)/(v_{i0} + ε) − 2 x̂]`. Stated for every `ε ≥ 0`. -/
theorem ineq_29 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hn : 0 < n)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidates I) xh yh)
    (i : ι) (ε : ℝ) (hε : 0 ≤ ε) (hnf : ∀ k, zhat I i ε k ∉ Set.Ioo (0 : ℝ) 1) :
    (I.vnp i + ε) ^ I.γ i * (Kval I i ε / (I.vnp i + ε) - 2 * xh) ≤ 2 * yh i := by sorry

end NestedLogitVariants.PartialCompetitive
