-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_productPMF_cons
-- name    : OAI.ThreeState.TreeClauses.Experiment.productPMF_cons
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:02:00.153815+00:00
-- url     : https://prove2.me/theorems/f3c6e1e6-a3a7-4445-a885-b94715fe7edf
-- title:
--   Sequential sampling of a product law: first coordinate, then the rest
-- statement:
--   Let $\alpha$ be a type, $n\in\mathbb{N}$, and $p_0,\dots,p_n$ discrete probability distributions on $\alpha$. Let $\bigotimes_{j\le n}p_j$ be the product law on $(n+1)$-tuples, with mass $\prod_jp_j(v_j)$. Then $\bigotimes_{j\le n}p_j$ equals the law of the tuple $(a,v_1,\dots,v_n)$ obtained as follows: draw $a\sim p_0$, then draw $(v_1,\dots,v_n)\sim\bigotimes_{j=1}^{n}p_j$ independently, and prepend $a$. In formulas,
--   $$
--   \Bigl(\bigotimes_{j=0}^{n}p_j\Bigr)(v)=p_0(v_0)\cdot\Bigl(\bigotimes_{j=1}^{n}p_j\Bigr)(v_1,\dots,v_n).
--   $$
--
--   This recursive description of independent products is what allows induction on the number of children.
--
--   **Formalization Note** Tuples are functions `Fin (n+1) → α`, and prepending is `Fin.cons`. The right-hand side is written as `(p 0).bind (fun a ↦ (productPMF (fun j ↦ p j.succ)).map (Fin.cons a))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/Products.lean#L70-L94

import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
variable {α β : Type*}

theorem OAI.ThreeState.TreeClauses.Experiment.productPMF_cons {n : ℕ} (p : Fin (n+1) → PMF α) :
    productPMF p = (p 0).bind (fun a ↦ (productPMF (fun j ↦ p j.succ)).map (Fin.cons a)) := by sorry
