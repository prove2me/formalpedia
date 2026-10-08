-- Prove2me | Theorems.Thm_NestedLogitVariants_PartialCompetitive_xh_nonneg
-- name    : NestedLogitVariants.PartialCompetitive.xh_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:07:58.439578+00:00
-- url     : https://prove2.me/theorems/e08ee93d-a249-4cbc-911c-676253cac81d
-- title:
--   Proof of Theorem 10, A.3, p. 45 — an optimal solution of (4) over the candidate collection has x̂ ≥ 0
-- statement:
--   Consider a nested logit instance with $\gamma_i \le 1$ for every nest and at least one product per nest. Let $(\hat x, \hat y)$ be an optimal solution of the linear program (4) in which the candidate collection of nest $i$ is $\{\hat S_i(\epsilon_i) : \epsilon_i \in [0,\infty]\} \cup \{\{j\} : j \in N\}$. Then
--
--   $$\hat x \ge 0.$$
--
--   This sign is what lets the proof of Theorem 10 compare the right sides of (4) at different capacities.
--
--   **Formalization Note** The hypothesis $n \ge 1$ (the paper's $N = \{1, \dots, n\}$ is nonempty) is the setting of the page's argument, which uses nonempty singleton assortments.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 45, Appendix A.3 (proof of Theorem 10), first paragraph

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

namespace NestedLogitVariants.PartialCompetitive

/-- Proof of Theorem 10 (A.3, p. 45): an optimal solution `(x̂, ŷ)` of (4) over the candidate
collections `{Ŝ_i(ε) : ε ∈ [0, ∞]} ∪ {{j} : j ∈ N}` has `x̂ ≥ 0`. -/
theorem xh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hn : 0 < n)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidates I) xh yh) :
    0 ≤ xh := by sorry

end NestedLogitVariants.PartialCompetitive
