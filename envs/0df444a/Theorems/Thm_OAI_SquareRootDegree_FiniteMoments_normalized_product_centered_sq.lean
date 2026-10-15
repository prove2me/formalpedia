-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_FiniteMoments_normalized_product_centered_sq
-- name    : OAI.SquareRootDegree.FiniteMoments.normalized_product_centered_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:46:29.981379+00:00
-- url     : https://prove2.me/theorems/0ec650e1-40ad-4363-96ba-aa5e92ade5e6
-- title:
--   Second moment of a sum of centred coordinates under a product of normalized weights
-- statement:
--   Let $\iota$ and $\alpha$ be finite sets and write $\mathbb E$ for uniform averages over finite sets. Let $r_i:\alpha\to\mathbb R$ ($i\in\iota$) satisfy $\mathbb E_{a\in\alpha}r_i(a)=1$ for every $i$, and let $T_i:\alpha\to\mathbb R$ be functions that are centred with respect to these weights, $\mathbb E_{a\in\alpha}\big[r_i(a)T_i(a)\big]=0$ for every $i\in\iota$. Then
--
--   $$
--   \mathbb E_{x\in\alpha^\iota}\Big[\Big(\prod_{i\in\iota}r_i(x_i)\Big)\Big(\sum_{i\in\iota}T_i(x_i)\Big)^2\Big]=\sum_{i\in\iota}\mathbb E_{a\in\alpha}\big[r_i(a)\,T_i(a)^2\big],
--   $$
--
--   where $x=(x_i)_{i\in\iota}$ ranges uniformly over $\alpha^\iota$.
--
--   This is the additivity of variance for independent centred summands, stated for product weights that need not be nonnegative: under the weight $\prod_i r_i(x_i)$ the coordinates behave like independent variables. It is the key step in computing the mean square of shifted sums under such weights.
--
--   **Formalization Note** Averages are `average` over a `Fintype`, and the product set is the function type `ι → α`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/FiniteMoments.lean#L67-L87

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection

open OAI OAI.SquareRootDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem OAI.SquareRootDegree.FiniteMoments.normalized_product_centered_sq (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (T : ι → α → ℝ) (hT : ∀ i, average (fun a => r i a*T i a) = 0) :
    average (fun x : ι → α => (∏ i, r i (x i))*(∑ i, T i (x i))^2) =
      ∑ i, average (fun a => r i a*(T i a)^2) := by sorry
