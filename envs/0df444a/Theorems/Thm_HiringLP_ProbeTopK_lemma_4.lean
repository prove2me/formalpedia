-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_lemma_4
-- name    : HiringLP.ProbeTopK.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:16.180876+00:00
-- url     : https://prove2.me/theorems/31aca55d-0b8a-4747-b3d4-18717e5ad303
-- title:
--   Lemma 4 — with two fractional components, DR beats independent rounding: inequality (5)
-- statement:
--   Let $I$ be a valid ProbeTop-k instance and let $(x, y)$ be a basic feasible solution of $\mathrm{LP}_{ptk}(I)$ with exactly two fractional components $i_1, i_2$. Interview in decreasing order of $v_i$ (ties in any order). Let $Y$ be the output of DR, and let $\tilde Y_1, \dots, \tilde Y_n$ be independent Bernoulli random variables with means $y_i$. With $P_i$ independent Bernoulli($p_i$) indicators independent of the rounding, set $Z_i = P_i Y_i$, $\tilde Z_i = P_i \tilde Y_i$, let $N_{i-1}$ count the $\ell$ before $i$ with $Z_\ell = 1$, and $\tilde N_{i-1} = \min\{k, \sum_{\ell \text{ before } i} \tilde Z_\ell\}$. Then
--
--   $$
--   \sum_{i=1}^n v_i\, \mathbb{E}\big(Z_i \mathbf 1\{N_{i-1} < k\}\big) \;\ge\; \sum_{i=1}^n v_i\, \mathbb{E}\big(\tilde Z_i \mathbf 1\{\tilde N_{i-1} < k\}\big). \tag{5}
--   $$
--
--   The correlation that DR creates between the two fractional applicants (exactly one of them is interviewed) can only help the algorithm compared with interviewing each independently.
--
--   **Formalization Note.** $\mathbf 1\{\min\{k, m\} < k\} = \mathbf 1\{m < k\}$, so the truncation in $\tilde N$ is dropped. The order is a permutation sorted by $v$ (`SortedBy`), which is the paper's relabelling $v_1 \ge \dots \ge v_n$ of p. 17.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 18, Lemma 4, inequality (5)

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_WeightedRank
import Definitions.Def_HiringLP_ProbeTopK_Model

namespace HiringLP.ProbeTopK

theorem lemma_4 {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I)) (hF : (fracSet y).card = 2)
    (ord : Equiv.Perm (Fin n)) (hord : SortedBy ord (vbar I x)) :
    cutValue I x y ord (indepProb y) ≤ cutValue I x y ord (DR y) := by sorry

end HiringLP.ProbeTopK
