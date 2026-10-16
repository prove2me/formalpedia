-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_partial_entropy_le
-- name    : OAI.CliqueFreeIndependence.FiniteEntropy.partial_entropy_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:26:37.994552+00:00
-- url     : https://prove2.me/theorems/276ebc0f-c031-4a13-b94f-268bbd1b12e1
-- title:
--   Partial weighted-entropy bound $\sum_{i\in s}p_i\log(w_i/p_i)\le t\log(m/t)$
-- statement:
--   Let $s$ be a finite set of indices, and let $w_i$ and $p_i$ ($i\in s$) be real numbers with $w_i>0$ and $p_i\ge0$ for every $i\in s$. Let $m>0$ satisfy $\sum_{i\in s}w_i\le m$, and put $t=\sum_{i\in s}p_i$. Then
--
--   $$
--   \sum_{i\in s}p_i\log\frac{w_i}{p_i}\le t\,\log\frac{m}{t},
--   $$
--
--   where $\log$ is the natural logarithm, terms with $p_i=0$ are read as $0$, and the right-hand side is read as $0$ when $t=0$.
--
--   For a probability vector $p$ supported on $s$ (so $t=1$) this is the classical bound that the weighted entropy $\sum_ip_i\log(w_i/p_i)$ is at most the logarithm of the total weight; the general form bounds the contribution of a part $s$ of the support carrying mass $t$, which is how entropy estimates are split between a light set and its complement. No bound $t\le1$ is required.
--
--   **Formalization Note** The index type need not be finite; only $s$ is a finite set (`Finset I`). When $t=0$, Lean's convention $\log(m/0)=\log0=0$ and the factor $t=0$ make the right-hand side $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean#L235-L272

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteEntropy
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {I : Type u} [Fintype I]
variable {J : Type v} [Fintype J]

omit [Fintype I] in
theorem OAI.CliqueFreeIndependence.FiniteEntropy.partial_entropy_le (s : Finset I) {w p : I → ℝ}
    (hw : ∀ i ∈ s, 0 < w i) (hp : ∀ i ∈ s, 0 ≤ p i)
    {m : ℝ} (hm : 0 < m) (hwm : ∑ i ∈ s, w i ≤ m) :
    (∑ i ∈ s, p i * Real.log (w i / p i)) ≤
      (∑ i ∈ s, p i) * Real.log (m / (∑ i ∈ s, p i)) := by sorry
