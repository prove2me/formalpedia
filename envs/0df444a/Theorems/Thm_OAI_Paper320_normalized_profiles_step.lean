-- Prove2me | Theorems.Thm_OAI_Paper320_normalized_profiles_step
-- name    : OAI.Paper320.normalized_profiles_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:08:33.346456+00:00
-- url     : https://prove2.me/theorems/44932cf3-369a-4d9d-b3d8-d32996b8d9e4
-- title:
--   Normalized maxima turn the four profile recurrences into two coupled scalar recurrences
-- statement:
--   For a real number $M > 0$, a level $n \in \mathbb{N}$ and real numbers $s_0, s_1$, the normalized maximum is
--   $$
--   \nu_M(n; s_0, s_1) = \max\Big( \frac{s_0}{M^n},\ \frac{s_1}{M^{n+1}} \Big).
--   $$
--   Let $r$ and $\varepsilon$ be real numbers with $r \ge 0$, $r/M \le \varepsilon$ and $16/M \le \varepsilon$. Let $s_0, s_1, j_0, j_1$ and $s_0', s_1', j_0', j_1'$ be real numbers with $s_0 \ge 0$ and $j_0 \ge 0$ that satisfy the four recurrence inequalities
--   $$
--   s_0' \le 16\, s_0 + s_1 + 3\, j_1, \qquad s_1' \le M^2 s_0 + r\, s_1, \qquad j_0' \le 16\, s_0 + 3\, j_1, \qquad j_1' \le M^2 j_0 + r\, s_1 .
--   $$
--   Write $u = \nu_M(n; s_0, s_1)$ and $v = \nu_M(n; j_0, j_1)$. Then:
--
--   1. $\nu_M(n+1; s_0', s_1') \le (1 + \varepsilon)\, u + 3\, v$;
--   2. $\nu_M(n+1; j_0', j_1') \le \varepsilon\, u + 3\, v$.
--
--   In the application, $(s_0, s_1)$ and $(j_0, j_1)$ are the side and joint sensitivity profiles (on rejected and on accepted inputs) of a family at level $n$ of the recursive construction, the primed quantities are the profiles at level $n+1$, and the hypotheses are the four profile recurrences, with $M^2$ the out-degree of the tournament and $r$ the number of labels. Normalizing by $M^n$ and $M^{n+1}$ compresses the four recurrences into two coupled scalar recurrences, in which the normalized side quantity grows only by the factor $1 + \varepsilon$ apart from the joint contribution.
--
--   **Formalization Note** $\nu_M(n; s_0, s_1)$ is `normalizedMax M n s₀ s₁`. Apart from $s_0 \ge 0$ and $j_0 \ge 0$, no sign conditions are imposed on the eight quantities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/ProfileArithmetic.lean#L62-L83

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

theorem OAI.Paper320.normalized_profiles_step {M r ε : ℝ} {n : ℕ}
    (hM : 0 < M) (hr : 0 ≤ r) (hεr : r / M ≤ ε) (hεt : 16 / M ≤ ε)
    {s₀ s₁ j₀ j₁ s₀' s₁' j₀' j₁' : ℝ} (hs₀ : 0 ≤ s₀) (hj₀ : 0 ≤ j₀)
    (hS₀ : s₀' ≤ 16 * s₀ + s₁ + 3 * j₁)
    (hS₁ : s₁' ≤ M ^ 2 * s₀ + r * s₁)
    (hJ₀ : j₀' ≤ 16 * s₀ + 3 * j₁)
    (hJ₁ : j₁' ≤ M ^ 2 * j₀ + r * s₁) :
    normalizedMax M (n + 1) s₀' s₁' ≤
      (1 + ε) * normalizedMax M n s₀ s₁ + 3 * normalizedMax M n j₀ j₁ ∧
    normalizedMax M (n + 1) j₀' j₁' ≤
      ε * normalizedMax M n s₀ s₁ + 3 * normalizedMax M n j₀ j₁ := by sorry
