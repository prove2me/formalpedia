-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_FiniteMoments_normalized_product_eval
-- name    : OAI.SquareRootDegree.FiniteMoments.normalized_product_eval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:45:29.368892+00:00
-- url     : https://prove2.me/theorems/14d84ca7-e214-4966-89ac-aca9808de6dd
-- title:
--   Coordinate marginal of a product of normalized weights
-- statement:
--   Let $\iota$ and $\alpha$ be finite sets, and for a function $u$ on a finite set $X$ write $\mathbb E_{x\in X}u(x)=|X|^{-1}\sum_{x\in X}u(x)$ for the uniform average. Let $r_i:\alpha\to\mathbb R$ ($i\in\iota$) be normalized weights, meaning $\mathbb E_{a\in\alpha}r_i(a)=1$ for every $i$; no sign condition is imposed. Then for every coordinate $j\in\iota$ and every function $g:\alpha\to\mathbb R$,
--
--   $$
--   \mathbb E_{x\in\alpha^\iota}\Big[\Big(\prod_{i\in\iota}r_i(x_i)\Big)\,g(x_j)\Big]=\mathbb E_{a\in\alpha}\big[r_j(a)\,g(a)\big],
--   $$
--
--   where $x=(x_i)_{i\in\iota}$ ranges uniformly over the product set $\alpha^\iota$.
--
--   In probabilistic language: if each $r_i$ is the density of a (possibly signed) measure on $\alpha$ with respect to the uniform distribution, then $\prod_i r_i(x_i)$ is the density of the product measure, and the $j$-th marginal of that product is the $j$-th factor. This is the basic evaluation rule behind the first- and second-moment computations for products of weights.
--
--   **Formalization Note** Averages are `average` over a `Fintype`, and the product set is the function type `ι → α`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/FiniteMoments.lean#L20-L35

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

theorem OAI.SquareRootDegree.FiniteMoments.normalized_product_eval (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (j : ι) (g : α → ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*g (x j)) = average (fun a => r j a*g a) := by sorry
