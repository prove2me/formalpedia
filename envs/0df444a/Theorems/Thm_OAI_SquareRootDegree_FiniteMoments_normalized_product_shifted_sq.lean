-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_FiniteMoments_normalized_product_shifted_sq
-- name    : OAI.SquareRootDegree.FiniteMoments.normalized_product_shifted_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:47:27.99495+00:00
-- url     : https://prove2.me/theorems/6163a299-87d3-4557-81bd-b5ba558edac9
-- title:
--   Mean square of a shifted sum under a product of normalized weights
-- statement:
--   Let $\iota$ and $\alpha$ be finite sets, write $\mathbb E$ for uniform averages, and let $r_i:\alpha\to\mathbb R$ satisfy $\mathbb E_{a\in\alpha}r_i(a)=1$ for all $i\in\iota$. Let $T_i:\alpha\to\mathbb R$ and $\mu_i\in\mathbb R$ be such that $\mathbb E_{a\in\alpha}[r_i(a)T_i(a)]=\mu_i$ for every $i$, and let $c\in\mathbb R$. Then
--
--   $$
--   \mathbb E_{x\in\alpha^\iota}\Big[\Big(\prod_{i\in\iota}r_i(x_i)\Big)\Big(c+\sum_{i\in\iota}T_i(x_i)\Big)^2\Big]=\Big(c+\sum_{i\in\iota}\mu_i\Big)^2+\sum_{i\in\iota}\Big(\mathbb E_{a\in\alpha}\big[r_i(a)T_i(a)^2\big]-\mu_i^2\Big),
--   $$
--
--   where $x=(x_i)_{i\in\iota}$ ranges uniformly over $\alpha^\iota$.
--
--   Reading the $r_i$ as (possibly signed) densities, $\mu_i$ is the weighted mean of $T_i$ and $\mathbb E[r_iT_i^2]-\mu_i^2$ its weighted variance, so the identity is the familiar decomposition "mean square equals squared mean plus the sum of the variances" for a shifted sum of independent variables. It is the moment identity from which the deficit of the soft switching events is computed in closed form.
--
--   **Formalization Note** Averages are `average` over a `Fintype`, and the product set is the function type `ι → α`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/FiniteMoments.lean#L89-L113

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

theorem OAI.SquareRootDegree.FiniteMoments.normalized_product_shifted_sq (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (T : ι → α → ℝ) (μ : ι → ℝ) (hμ : ∀ i, average (fun a => r i a*T i a) = μ i)
    (c : ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*(c+∑ i, T i (x i))^2) =
      (c+∑ i, μ i)^2 + ∑ i, (average (fun a => r i a*(T i a)^2)-(μ i)^2) := by sorry
