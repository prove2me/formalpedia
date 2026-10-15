-- Prove2me | Theorems.Thm_OAI_Paper320_coupled_profiles_bound
-- name    : OAI.Paper320.coupled_profiles_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:09:15.646873+00:00
-- url     : https://prove2.me/theorems/51de0b85-940f-437b-8443-ff2ccd7edcb2
-- title:
--   Bounded growth for two coupled linear recurrence inequalities under a geometric budget
-- statement:
--   Let $d \in \mathbb{N}$ and let $\varepsilon, L$ be real numbers with $\varepsilon \ge 0$, $L \ge 0$ and the budget condition $\varepsilon \cdot 3^{d+1} \le 2$. Let $(u_n)_{n \ge 0}$ and $(v_n)_{n \ge 0}$ be sequences of real numbers with $u_0 \le L$ and $v_0 \le 0$ such that, for every $n < d$,
--   $$
--   u_{n+1} \le (1 + \varepsilon)\, u_n + 3\, v_n, \qquad v_{n+1} \le \varepsilon\, u_n + 3\, v_n .
--   $$
--   Then for every $n \le d$,
--   $$
--   u_n \le 2L \qquad \text{and} \qquad v_n \le \varepsilon L\, (3^n - 1).
--   $$
--
--   The sequence $v$ acts as an error term that may triple at every step, and the budget condition guarantees that the accumulated error over $d$ steps stays below $L$, so that $u$ at most doubles. In the sensitivity analysis of the recursive construction, $u_n$ and $v_n$ are the normalized side and joint sensitivity profiles at level $n$, and the theorem keeps the normalized side profile bounded over all $d$ levels.
--
--   **Formalization Note** The sequences are arbitrary functions from $\mathbb{N}$ to $\mathbb{R}$; their terms with index larger than $d$ are unconstrained, and the conclusion concerns only $n \le d$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/ScalarBounds.lean#L19-L50

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

theorem OAI.Paper320.coupled_profiles_bound (d : ℕ) (u v : ℕ → ℝ) (ε L : ℝ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2)
    (hu0 : u 0 ≤ L) (hv0 : v 0 ≤ 0)
    (hu : ∀ n < d, u (n + 1) ≤ (1 + ε) * u n + 3 * v n)
    (hv : ∀ n < d, v (n + 1) ≤ ε * u n + 3 * v n) :
    ∀ n ≤ d, u n ≤ 2 * L ∧ v n ≤ ε * L * (3 ^ n - 1) := by sorry
