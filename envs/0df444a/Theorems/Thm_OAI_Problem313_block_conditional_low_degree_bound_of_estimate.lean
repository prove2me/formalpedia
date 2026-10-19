-- Prove2me | Theorems.Thm_OAI_Problem313_block_conditional_low_degree_bound_of_estimate
-- name    : OAI.Problem313.block_conditional_low_degree_bound_of_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:48:22.306574+00:00
-- url     : https://prove2.me/theorems/9effa65f-0cd9-42e9-b052-b6a054fb2035
-- title:
--   Low-degree mass of block restrictions of a symmetric graph property
-- statement:
--   Let $f$ be a vertex-invariant graph property on $n$ vertices, $B$ a vertex block with $|B|\ge3$, $0\le p\le1$, and $k,C\in\mathbb{R}$. For an exterior configuration $y$ on the edges not touching $B$, let $f_y$ be the restriction of $f$ to the edges touching $B$. Suppose every Boolean function $g$ of the touching edges whose influences satisfy $I_e^p(g)\le\frac1{|B|}\sum_dI_d^p(g)$ obeys
--   $$
--   \sum_{A\ne\emptyset,\ |A|\le k}\hat g(A)^2\le C\sum_eI_e^p(g) .
--   $$
--   Then
--   $$
--   \sum_yw_p(y)\sum_{A\ne\emptyset,|A|\le k}\widehat{f_y}(A)^2\le C\sum_{e\text{ touching }B}I_e^p(f) .
--   $$
--
--   Restrictions to a block inherit enough symmetry from vertex invariance to apply the low-degree estimate. Averaging over the exterior gives the influences of $f$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockLowDegree.lean#L90-L128

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation

open OAI OAI.Problem313
universe u
open scoped BigOperators

theorem OAI.Problem313.block_conditional_low_degree_bound_of_estimate
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p k C : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hestimate : ∀ g : ({e : GraphEdge n // EdgeTouches B e} → Bool) → Bool,
      (∀ e, Reindex.influence p g e ≤
        (∑ d, Reindex.influence p g d) / (B.card : ℝ)) →
      (∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p (fun x => boolReal (g x)) A ^ 2 else 0) ≤
      C * ∑ e, Reindex.influence p g e) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      BiasedFourier.weight p y *
        ∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
          if A.Nonempty ∧ (A.card : ℝ) ≤ k then
            BiasedFourier.coeff p
              (fun x => boolReal (restrictCube (EdgeTouches B) f y x)) A ^ 2
          else 0) ≤
      C * ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by sorry
