-- Prove2me | Theorems.Thm_NisanRonen_Rounding_bonus_max_minimal_execution
-- name    : NisanRonen.Rounding.bonus_max_minimal_execution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:27:12.009477+00:00
-- url     : https://prove2.me/theorems/56e31ec5-0bf9-4a16-8992-86f0335b446b
-- title:
--   Executing in minimal time maximizes the rounded bonus
-- statement:
--   Let $\delta > 0$, $x$ an allocation, $d$ a matrix of declarations, $i$ an agent of type $t^i$, and $\tilde t$ a vector of actual times with $\tilde t_j \ge t^i_j$ for every task $j \in x^i$. Then
--
--   1. $\hat g\big(x, \mathrm{corr}^i(x, d, t^i)\big) \le \hat g\big(x, \mathrm{corr}^i(x, d, \tilde t)\big)$, so the bonus $-\hat g(x, \mathrm{corr}^i)$ is largest when agent $i$ executes its tasks in minimal time;
--   2. $\mathrm{corr}^i(x, d, t^i) = \mathrm{corr}^*\big(x, (d^{-i}, t^i)\big)$: with minimal execution the corrected time vector is the vector $\mathrm{corr}^*$ of the declarations in which agent $i$'s declaration is replaced by its type.
--
--   Differences from the source:
--   - encoding: agents 1, …, n and tasks 1, …, k → `Fin n` and `Fin k`, i.e. 0, …, n − 1 and 0, …, k − 1; reason: Lean indexing convention; the same instances
--   - encoding: n agents → `[NeZero n]`, i.e. n ≥ 1; reason: with no agents and at least one task there is no allocation and no make-span; the paper's n agents are at least one
--   - reading: the argument of Claim 5.2 for the exact bonus −g(x(t), corr^i(x(t), t, t̃)) of Definition 23 → the same step for the rounded bonus −ĝ(x(t̂), corr^i(x(t), t, t̃)) of Definition 34; reason: the proof sketch of Theorem 5.9 (p. 193) applies "Arguments similar to those in 5.1" to the rounding mechanism; this is that argument's step for ĝ
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, proof of Claim 5.2, p. 188 (PDF p. 23): "for every allocation x the bonus for an agent i is maximized when executing its assignments in minimal time", applied to the rounded bonus of Definition 34, p. 193

import Mathlib
import Definitions.Def_NisanRonen_Rounding_roundedMakespan
import Definitions.Def_NisanRonen_Rounding_corr
import Definitions.Def_NisanRonen_Rounding_corrStar

namespace NisanRonen.Rounding

/-- **Minimal execution maximizes the bonus** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), proof of Claim 5.2, p. 188:
"for every allocation x the bonus for an agent i is maximized when executing its assignments in
minimal time"), for the rounded bonus of Definition 34 (p. 193). Let `δ > 0`, `x` an allocation,
`d` the declarations, `i` an agent of type `t^i`, and `t̃` actual times with `t̃_j ≥ t^i_j` for every
task `j` allocated to `i`. Then

1. `ĝ(x, corr^i(x, d, t^i)) ≤ ĝ(x, corr^i(x, d, t̃))`, so executing in minimal time gives the
   largest bonus `−ĝ(x, corr^i)`;
2. `corr^i(x, d, t^i) = corr*(x, (d^{−i}, t^i))`: with minimal execution the corrected time
   vector is the corr* vector of the declarations with agent `i`'s replaced by its type. -/
theorem bonus_max_minimal_execution {n k : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ)
    (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) (i : Fin n) (ti tt : Fin k → ℝ)
    (htt : ∀ j, x j = i → ti j ≤ tt j) :
    roundedMakespan δ x (corr i x d ti) ≤ roundedMakespan δ x (corr i x d tt) ∧
      corr i x d ti = corrStar x (Function.update d i ti) := by sorry

end NisanRonen.Rounding
