-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_SmoothSelector_hat_local
-- name    : OAI.SquareRootDegree.SmoothSelector.hat_local
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:51:43.381984+00:00
-- url     : https://prove2.me/theorems/c9da4844-a01e-458e-8a58-3913f7708bfe
-- title:
--   Grid hat functions are localized: a nonzero hat value forces $|c_i-(1+t)|<\delta$
-- statement:
--   Let $\operatorname{clip}(x)=\max(0,\min(1,x))$ be the clamp of $x$ to $[0,1]$. For $N\in\mathbb N$, a step $\delta\in\mathbb R$ and an index $i\in\{0,1,\dots,2N\}$, define the hat function and the grid centre
--   $$\operatorname{hat}_{N,\delta,i}(t)=\operatorname{clip}\Big(\frac t\delta+N-i+1\Big)-\operatorname{clip}\Big(\frac t\delta+N-i\Big),\qquad c_{N,\delta}(i)=1+\delta\,(i-N).$$
--   If $\delta>0$, then for every $t\in\mathbb R$ and every index $i$,
--
--   $$
--   \operatorname{hat}_{N,\delta,i}(t)\neq0\ \Longrightarrow\ \big|c_{N,\delta}(i)-(1+t)\big|<\delta .
--   $$
--
--   For $\delta>0$ the function $\operatorname{hat}_{N,\delta,i}$ is the piecewise-linear tent of height $1$ peaked at $t=\delta(i-N)$, vanishing outside the open interval of radius $\delta$ around that point; the statement says it is nonzero only when the shifted point $1+t$ lies strictly within distance $\delta$ of the $i$-th grid centre. The $2N+1$ hats form a partition of unity on $[-N\delta,N\delta]$, and this localisation is what makes a selector built from them choose only grid points close to $1+t$; it also shows that every hat has compact support.
--
--   **Formalization Note** $\operatorname{hat}$ and $c$ are `hat N δ i` and `center N δ i`, with `i : Fin (2*N+1)` cast to a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/SmoothSelector.lean#L89-L104

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.SmoothSelector
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

theorem OAI.SquareRootDegree.SmoothSelector.hat_local {N : ℕ} {δ t : ℝ} {i : Fin (2*N+1)} (hδ : 0 < δ)
    (hi : hat N δ i t ≠ 0) : |center N δ i-(1+t)| < δ := by sorry
