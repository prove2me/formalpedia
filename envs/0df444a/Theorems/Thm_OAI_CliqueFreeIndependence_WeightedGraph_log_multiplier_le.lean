-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_log_multiplier_le
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.log_multiplier_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:26:35.999413+00:00
-- url     : https://prove2.me/theorems/dc178575-ce13-41de-995f-3850868d7226
-- title:
--   Logarithmic size of the multiplier bound at precision $e^{-8x}$
-- statement:
--   For $k\in\mathbb N$ and $\varepsilon>0$ let $b_k(\varepsilon)=2^{(k+2)k}/\varepsilon^{k}$; this is the bound on the random multipliers available for $K_{k+2}$-free vertex sets at precision $\varepsilon$. Then for every natural number $k$ and every real number $x\ge1$,
--
--   $$
--   \log\Big(1+e^{4x}\,b_k\big(e^{-8x}\big)\Big)\le\big(5+10k+k^2\big)\,x ,
--   $$
--
--   where $\log$ is the natural logarithm.
--
--   This numerical estimate is used when the variational cross-mass inequality at an optimizer is applied with scaling factor $e^{4x}$ and multiplier precision $e^{-8x}$: it turns the logarithmic term $\log(1+e^{4x}b_k(e^{-8x}))$ into a bound that is linear in $x$, with a constant quadratic in $k$.
--
--   **Formalization Note** $b_k(\varepsilon)$ is `multiplierBound k ε`, and $\log$ is `Real.log`; the argument of the logarithm is at least $1$, so no logarithm conventions are involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/DisjointCross.lean#L18-L48

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Lottery
universe u
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.log_multiplier_le (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log (1 + Real.exp (4*x) * multiplierBound k (Real.exp (-8*x))) ≤
      (5 + 10*(k:ℝ) + (k:ℝ)^2)*x := by sorry
