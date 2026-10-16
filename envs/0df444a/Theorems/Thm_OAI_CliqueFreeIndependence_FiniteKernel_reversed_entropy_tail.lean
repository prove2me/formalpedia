-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteKernel_reversed_entropy_tail
-- name    : OAI.CliqueFreeIndependence.FiniteKernel.reversed_entropy_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:41:36.072494+00:00
-- url     : https://prove2.me/theorems/f9f9e317-a016-46c8-85b9-759e3619a95f
-- title:
--   Average entropy controls the reversed low-density tail of a reversible kernel
-- statement:
--   Let $I$ be a finite set and $w:I\to\mathbb{R}$ a positive weight ($w_i>0$ for all $i$). For a probability vector $p$ on $I$ define the $w$-weighted entropy $H_w(p)=\sum_{j\in I}p_j\log(w_j/p_j)$, with the convention that terms with $p_j=0$ vanish. Let $\mu$ be a probability vector on $I$ ($\mu_i\ge0$, $\sum_i\mu_i=1$) and let $K=(K_{ij})$ be a stochastic matrix on $I$ (nonnegative entries, every row summing to $1$) that is *reversible* with respect to $\mu$, i.e. $\mu_iK_{ij}=\mu_jK_{ji}$ for all $i,j$. The *average entropy* of $K$ is $\overline H_{\mu,w}(K)=\sum_{i}\mu_i\,H_w(K_{i\cdot})$, where $K_{i\cdot}$ denotes the $i$-th row.
--
--   Let $x>0$ and assume that $K$ has density at most $x$ with respect to $w$: $K_{ij}\le x\,w_j$ for all $i,j\in I$. Then for every real number $a$,
--
--   $$
--   (a+\log x)\sum_{i\in I}\mu_i\sum_{j\in I}\mathbf 1\!\left[K_{ji}<w_i\,e^{-a}\right]K_{ij}\;\le\;\overline H_{\mu,w}(K)+\log x .
--   $$
--
--   Probabilistically, let $(X,Y)$ be one step of the chain started from $\mu$, so that $\Pr(X=i,\,Y=j)=\mu_iK_{ij}$. The double sum on the left is the probability that the *reverse* transition is unlikely, $K_{YX}<w_X\,e^{-a}$. So whenever $a+\log x>0$ this probability is at most $(\overline H_{\mu,w}(K)+\log x)/(a+\log x)$: a reversible kernel with small average entropy rarely makes a step that it would be unlikely to undo. This is the estimate that turns an entropy bound for a smoothed random walk into a bound on the mass of badly reversed transitions.
--
--   **Formalization Note** $H_w$ is `entropy w`, $\overline H_{\mu,w}(K)$ is `avgEntropy μ w K`, the indicator sum is written with `if … then … else 0`, and the logarithm is `Real.log`. Lean's conventions $w_j/0=0$ and $\log 0=0$ give the convention for zero entries. No sign condition on $a+\log x$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean#L388-L411

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
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteKernel
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
open FiniteEntropy
variable {I : Type u} [Fintype I]
variable {J : Type v}
attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI

theorem OAI.CliqueFreeIndependence.FiniteKernel.reversed_entropy_tail {μ w : I → ℝ} {K : Matrix I I ℝ}
    (hμ : IsProb μ) (hw : ∀ i, 0 < w i) (hK : Stochastic K)
    (hr : Reversible μ K) {x a : ℝ} (hx : 0 < x)
    (hd : ∀ i j, K i j ≤ x * w j) :
    (a + Real.log x) *
        (∑ i, μ i * ∑ j, if K j i < w i * Real.exp (-a) then K i j else 0) ≤
      avgEntropy μ w K + Real.log x := by sorry
