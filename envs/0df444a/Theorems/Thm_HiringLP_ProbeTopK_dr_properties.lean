-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_dr_properties
-- name    : HiringLP.ProbeTopK.dr_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:26.643782+00:00
-- url     : https://prove2.me/theorems/132fbc4a-f7cd-41ab-9c05-13d3311baad3
-- title:
--   §4.2, p. 17 — DR is a distribution with E(Y_i) = y_i (P1) and Σ_i Y_i ≤ T almost surely (P2)
-- statement:
--   Let $I$ be a valid ProbeTop-k instance and let $(x, y)$ be a basic feasible solution of $\mathrm{LP}_{ptk}(I)$. Let $\mathrm{DR}(S)$ denote the probability that the dependent rounding DR applied to $y$ outputs the interview set $S \subseteq [n]$ (so $Y_i = \mathbf 1\{i \in S\}$). Then $\mathrm{DR}$ is a probability distribution,
--
--   $$
--   \mathrm{DR}(S) \ge 0 \ \text{ for all } S, \qquad \sum_{S \subseteq [n]} \mathrm{DR}(S) = 1,
--   $$
--
--   and it satisfies
--
--   1. **(P1)** $\mathbb{E}(Y_i) = \sum_{S \ni i} \mathrm{DR}(S) = y_i$ for every $i \in [n]$;
--   2. **(P2)** every outcome $S$ with $\mathrm{DR}(S) \neq 0$ has $|S| = \sum_i Y_i \le T$.
--
--   These two properties are all the analysis of ALGptk uses about the rounding: the marginals of the interview indicators are the LP's $y_i$, and the interview budget is never exceeded.
--
--   **Formalization Note.** DR is given by an explicit formula on subsets of `Fin n`; the statement is posed at extreme points, where the formula is the paper's procedure (at most two fractional coordinates, by Lemma 2). The distribution facts (non-negativity, total mass $1$) are included because the page's "it is easy to see" covers them.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 17, §4.2, properties (P1) and (P2)

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

namespace HiringLP.ProbeTopK

theorem dr_properties {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I)) :
    (∀ S, 0 ≤ DR y S) ∧ (∑ S, DR y S = 1) ∧
      (∀ i, ∑ S, DR y S * (if i ∈ S then 1 else 0) = y i) ∧
      ∀ S, DR y S ≠ 0 → S.card ≤ I.T := by sorry

end HiringLP.ProbeTopK
