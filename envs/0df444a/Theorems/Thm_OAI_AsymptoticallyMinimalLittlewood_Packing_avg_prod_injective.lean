-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_avg_prod_injective
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.avg_prod_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:23:21.863255+00:00
-- url     : https://prove2.me/theorems/9c4bc6ce-1322-49dc-b8e3-e8eb7d1ac9a4
-- title:
--   Averages over $A^K$ of products of functions of distinct coordinates factor
-- statement:
--   For a nonempty finite set $X$ and a function $h:X\to\mathbb R$ write
--   $\operatorname{avg}_{x\in X}h(x)=\frac{1}{|X|}\sum_{x\in X}h(x)$ for the uniform average.
--
--   Let $K$, $J$ and $A$ be finite sets with $A$ nonempty, let $\kappa:J\to K$ be an injective map, and let $f_j:A\to\mathbb R$ ($j\in J$) be real-valued functions. Then, averaging over all maps $\omega:K\to A$,
--
--   $$
--   \operatorname{avg}_{\omega\in A^{K}}\ \prod_{j\in J} f_j\big(\omega(\kappa(j))\big)\;=\;\prod_{j\in J}\ \operatorname{avg}_{x\in A} f_j(x).
--   $$
--
--   In probabilistic language: if $\omega$ is a uniformly random map $K\to A$, then its values at distinct points are independent and uniformly distributed on $A$, so the expectation of a product of functions of distinct coordinates factors into the product of expectations. When $J$ is empty both sides equal $1$.
--
--   This is the basic independence computation behind the moment estimates for random slot choices, where products of indicator functions of events $\omega(\kappa(j))=a_j$ at distinct coordinates are averaged.
--
--   **Formalization Note** `avg h` is defined as the sum of $h$ over the finite type divided by its cardinality. The averaged type here is the function type `K → A`, which is finite (using `Fintype K`, `DecidableEq K` and `Fintype A`) and nonempty because $A$ is.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Averages.lean#L74-L101

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uΩ uI uΛ uK uA uJ uY
open scoped BigOperators
open Finset
variable {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.avg_prod_injective {K : Type uK} {J : Type uJ} {A : Type uA} [Fintype K] [DecidableEq K] [Fintype J] [Fintype A]
    [Nonempty A] (κ : J → K) (hκ : Function.Injective κ) (f : J → A → ℝ) :
    avg (fun ω : K → A ↦ ∏ j, f j (ω (κ j))) = ∏ j, avg (f j) := by sorry
