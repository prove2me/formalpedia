-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_productPMF_list
-- name    : OAI.ThreeState.TreeClauses.Tree.productPMF_list
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:04:25.341555+00:00
-- url     : https://prove2.me/theorems/2160257b-2a87-4a27-a256-baa148510a76
-- title:
--   Listing an i.i.d. tuple gives the i.i.d. list law
-- statement:
--   Let $\alpha$ be a type, $p$ a discrete probability distribution on $\alpha$, and $n\in\mathbb{N}$. Let $p^{\otimes n}$ be the law of an $n$-tuple $(v_0,\dots,v_{n-1})$ of independent draws from $p$, and $\mathrm{IID}_n(p)$ the law of a list of $n$ independent draws, defined recursively by prepending a fresh draw. Then the image of $p^{\otimes n}$ under $(v_0,\dots,v_{n-1})\mapsto[v_0,\dots,v_{n-1}]$ is $\mathrm{IID}_n(p)$:
--   $$
--   \bigl(p^{\otimes n}\bigr)\circ\mathrm{list}^{-1}=\mathrm{IID}_n(p).
--   $$
--
--   This identifies the product-measure description of $n$ independent children with the list-based description used in the definition of the observation law.
--
--   **Formalization Note** The list map is `List.ofFn`, and $\mathrm{IID}_n(p)$ is `iidList p n` from the mission's definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/RegularLaw.lean#L54-L72

import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Experiment

theorem OAI.ThreeState.TreeClauses.Tree.productPMF_list {α : Type} (p : PMF α) (n : ℕ) :
    (productPMF (fun _ : Fin n ↦ p)).map List.ofFn = iidList p n := by sorry
