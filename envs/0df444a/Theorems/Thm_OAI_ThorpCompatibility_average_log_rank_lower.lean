-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_average_log_rank_lower
-- name    : OAI.ThorpCompatibility.average_log_rank_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:42:06.942099+00:00
-- url     : https://prove2.me/theorems/613c07ce-fb52-42bb-835f-a1720fbd9310
-- title:
--   Average of $-\log\frac{D-t}{D}$ over the ranks $t<D$ is at least $1-\frac{1+\log D}{D}$
-- statement:
--   Let $D\ge1$ be an integer. Then
--
--   $$
--   \frac1D\sum_{t=0}^{D-1}\Big(-\log\frac{D-t}{D}\Big)\;\ge\;1-\frac{1+\log D}{D}.
--   $$
--
--   Equivalently, if $T$ is uniformly distributed on $\{0,1,\dots,D-1\}$, the expected value of $-\log\frac{D-T}{D}$ (the negative logarithm of the fraction of ranks that are at least $T$) is at least $1-\frac{1+\log D}{D}$. Since $\frac{D-T}{D}$ is a discrete analogue of a uniform random variable $U$ on $(0,1]$, for which $\mathbb E[-\log U]=1$, the bound says that the discrete average falls short of the continuous value by at most $\frac{1+\log D}{D}$.
--
--   This estimate supplies the main term in a lower bound for the expected surprisal of an exclusion event under a uniformly random ordering, in which the rank of a distinguished element is uniform.
--
--   **Formalization Note** The quantity $D-t$ is a natural-number subtraction cast to $\mathbb{R}$; since $t<D$ it is never truncated.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/LogEstimates.lean#L67-L83

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.average_log_rank_lower {D : ℕ} (hD : 0 < D) :
    1 - (1 + Real.log (D : ℝ)) / (D : ℝ) ≤
      (∑ t : Fin D, -Real.log (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ))) / D := by sorry
