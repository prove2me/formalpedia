-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_center_bounds_eventually
-- name    : OAI.FixedClauseThreshold.center_bounds_eventually
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:01:53.199155+00:00
-- url     : https://prove2.me/theorems/b2f39145-f953-48bb-b2dc-ed444b12b5db
-- title:
--   The normalized lifetime center of random $k$-SAT is eventually between $e^{-2}/16$ and $2^k+1$
-- statement:
--   Fix $k\ge3$. For $n\ge1$ let $M=2^{k+1}n$ and let $C_1,\dots,C_M$ be independent uniformly random proper $k$-clauses on the Boolean variables $x_1,\dots,x_n$; a proper $k$-clause is a choice of $k$ distinct variables with a sign (a required truth value) for each, satisfied by an assignment that agrees with at least one of the signs. Let
--
--   $$
--   \Lambda=\#\big\{j\in\{1,\dots,M\}:\ C_1,\dots,C_j\text{ are simultaneously satisfiable}\big\}
--   $$
--
--   be the capped lifetime and $c_{n,k}=\mathbb E[\Lambda]/n$ its normalized center. Then there is $N$ such that for all $n\ge N$
--
--   $$
--   \frac{e^{-2}}{16}\ \le\ c_{n,k}\ \le\ 2^k+1 .
--   $$
--
--   Thus the centers eventually stay in a fixed compact subinterval of $(0,\infty)$. Since the satisfiability probability with $m\le M$ clauses equals $\Pr[\Lambda\ge m]$ and $\Lambda$ concentrates around $nc_{n,k}$, these bounds keep the candidate threshold densities away from $0$ and from $\infty$, so that a threshold obtained as a limit of the centers is positive and finite.
--
--   **Formalization Note** The statement is an eventually-statement (`Filter.Eventually` along `Filter.atTop`). The lower bound is `lowerCenterBound` $=$ `smallDensity / 4` with `smallDensity` $=e^{-2}/4$, and $c_{n,k}$ is `center n k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/CenterBounds.lean#L501-L514

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.center_bounds_eventually (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in Filter.atTop, lowerCenterBound ≤ center n k ∧ center n k ≤ (2 : ℝ)^k + 1 := by sorry
