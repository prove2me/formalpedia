-- Prove2me | Theorems.Thm_NestedLogitVariants_General_shat_mem_candidatesPR
-- name    : NestedLogitVariants.General.shat_mem_candidatesPR
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:42:32.249054+00:00
-- url     : https://prove2.me/theorems/0ae5c312-0657-46f9-b152-b349412a9a00
-- title:
--   pp. 24–25 — every greedy knapsack assortment Ŝ_i(ε_i) is one of the N^k_ij
-- statement:
--   Fix a nest $i$ of an instance satisfying the standing assumptions with at least one product, and a capacity $\epsilon_i\ge0$. Let $\hat S_i(\epsilon_i)$ be the assortment of products taken fully by the greedy solution of the continuous knapsack problem (11). Then $\hat S_i(\epsilon_i)$ belongs to the candidate collection of Theorem 11:
--   $$
--   \hat S_i(\epsilon_i)\in\{N^k_{ij} : k\in N,\ j=0,\dots,k\}\cup\{\{j\} : j\in N\}.
--   $$
--   In fact it is one of the $N^k_{ij}$: with $k$ the number of products whose preference weights do not exceed $\epsilon_i$, the greedy rule fills the knapsack with the highest-revenue products among the $k$ lightest ones.
--
--   This is what makes the collection of Theorem 11 contain the candidate assortments of §5, so that the argument of Theorem 10 applies in the nests with $\gamma_i\le1$.
--
--   **Formalization Note** The hypothesis $n\ge1$ is added: for $n=0$ the collection is empty (there is no $k\in\{1,\dots,n\}$) while $\hat S_i(\epsilon_i)=\emptyset$. When no product is eligible, $\hat S_i(\epsilon_i)=\emptyset=N^1_{i0}$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 24–25, §5, the inclusion {Ŝ_i(ε_i) : ε_i ∈ [0, ∞]} ⊂ {N^k_ij : k ∈ N, j = 0, …, k}

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_NestedPR
import Definitions.Def_NestedLogitVariants_General_Knapsack

namespace NestedLogitVariants.General

/-- pp. 24–25: for every capacity `ε ≥ 0`, the greedy assortment `Ŝ_i(ε)` of the continuous
knapsack (11) is one of the assortments `N^k_ij` (`k ∈ N`, `j = 0, …, k`), hence a member of the
candidate collection of Theorem 11. -/
theorem shat_mem_candidatesPR {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hn : 0 < n) (i : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    Shat I i ε ∈ candidatesPR I i := by sorry

end NestedLogitVariants.General
