-- Prove2me | Theorems.Thm_OAI_Paper320_quantitative_profile_bounds
-- name    : OAI.Paper320.quantitative_profile_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:09:58.626042+00:00
-- url     : https://prove2.me/theorems/34faca99-53cc-4843-b989-0c68389c71ad
-- title:
--   Profiles obeying the four sensitivity recurrences grow at most like $2LM^n$ and $2LM^{n+1}$
-- statement:
--   Let $d, L, M, r$ be natural numbers with $M \ge 1$ that satisfy the budget condition
--   $$
--   \frac{\max(r, 16)}{M} \cdot 3^{d+1} \le 2,
--   $$
--   evaluated in the real numbers. For $n \in \mathbb{N}$ and $b \in \{0,1\}$ let $S_n(b)$ and $J_n(b)$ be natural numbers with initial values
--   $$
--   S_0(0) \le L, \qquad S_0(1) \le LM, \qquad J_0(0) = J_0(1) = 0,
--   $$
--   and suppose that for every $n < d$ the four recurrences
--   $$
--   S_{n+1}(0) \le 16\, S_n(0) + S_n(1) + 3\, J_n(1), \qquad S_{n+1}(1) \le M^2 S_n(0) + r\, S_n(1),
--   $$
--   $$
--   J_{n+1}(0) \le 16\, S_n(0) + 3\, J_n(1), \qquad J_{n+1}(1) \le M^2 J_n(0) + r\, S_n(1)
--   $$
--   hold. Then for every $n \le d$,
--   $$
--   S_n(0) \le 2 L M^n \qquad \text{and} \qquad S_n(1) \le 2 L M^{n+1}.
--   $$
--
--   This is the abstract growth bound behind the sensitivity estimate of the recursive construction: $S_n(0)$ and $S_n(1)$ play the role of the side sensitivity profiles on rejected and on accepted inputs after $n$ levels, $J_n(b)$ that of the joint profiles, and the recurrences are those satisfied along the tower built from a regular tournament with out-degree $M^2$ and a good labeling with $r$ labels. Over $d$ levels the sensitivity on rejected inputs grows at most like $M^n$ and on accepted inputs at most like $M^{n+1}$, with a loss of only a factor $2$ relative to the initial bound $L$.
--
--   **Formalization Note** The profiles are functions `S J : ℕ → Bool → ℕ`, with `false` and `true` standing for $0$ and $1$; the budget casts the natural number `max r 16` to $\mathbb{R}$, and $M \ge 1$ is `0 < M`. Only the levels $n \le d$ are constrained.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/QuantitativeProfiles.lean#L12-L56

import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic

open OAI OAI.Paper320

theorem OAI.Paper320.quantitative_profile_bounds (d L M r : ℕ) (hM : 0 < M)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2)
    (S J : ℕ → Bool → ℕ)
    (hS₀ : S 0 false ≤ L) (hS₁ : S 0 true ≤ L * M)
    (hJ₀ : J 0 false = 0) (hJ₁ : J 0 true = 0)
    (hstepS₀ : ∀ n < d, S (n + 1) false ≤ 16 * S n false + S n true + 3 * J n true)
    (hstepS₁ : ∀ n < d, S (n + 1) true ≤ M ^ 2 * S n false + r * S n true)
    (hstepJ₀ : ∀ n < d, J (n + 1) false ≤ 16 * S n false + 3 * J n true)
    (hstepJ₁ : ∀ n < d, J (n + 1) true ≤ M ^ 2 * J n false + r * S n true) :
    ∀ n ≤ d, S n false ≤ 2 * L * M ^ n ∧ S n true ≤ 2 * L * M ^ (n + 1) := by sorry
