-- Prove2me | Theorems.Thm_OAI_Problem313_graph_fourier_capture_of_block_bounds
-- name    : OAI.Problem313.graph_fourier_capture_of_block_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:49:44.318881+00:00
-- url     : https://prove2.me/theorems/5896f1d0-b27d-4073-8fa2-6262d663c391
-- title:
--   Global low-level Fourier mass from block estimates
-- statement:
--   For a graph property $f$ on $n$ labelled vertices and $0<p<1$, let $\hat f(S)$ be the $p$-biased Fourier coefficients of $[f]$ over edge sets $S$, $I_e^p(f)$ the probability that edge $e$ is pivotal, and $I^p(f)=\sum_eI_e^p(f)$. An edge touches a vertex block $B$ if it has an endpoint in $B$. Let $1\le m\le n$, $k\in\mathbb{R}$, $a\ge0$, and call a block $B$ detecting for $S$ if $1\le|\{e\in S:e\text{ touches }B\}|\le k$. Assume:
--
--   1. every nonempty $S$ with $|S|\le k^2/2$ is detected by a uniformly random $m$-block with probability at least $m/(2n)$;
--   2. every $m$-block $B$ satisfies $\sum_{S\text{ detected by }B}\hat f(S)^2\le a\sum_{e\text{ touches }B}I_e^p(f)$.
--
--   Then
--   $$
--   \sum_{S\ne\emptyset,\ |S|\le k^2/2}\hat f(S)^2\le4a\,I^p(f) .
--   $$
--
--   No single block needs to capture all supports. It suffices that each support is captured often and that each block's captured mass is controlled.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/GraphBlockAverage.lean#L17-L90

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
open scoped BigOperators Classical

theorem OAI.Problem313.graph_fourier_capture_of_block_bounds
    {n m : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hmn : m ≤ n)
    (k a : ℝ) (ha : 0 ≤ a)
    (hcapture : ∀ S : Finset (GraphEdge n), S.Nonempty →
      (S.card : ℝ) ≤ k ^ 2 / 2 →
      (m : ℝ) / (2 * n) ≤
        blockProbability (Finset.univ : Finset (Fin n)) m (fun B =>
          1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤ k))
    (hblock : ∀ B : Finset (Fin n), B.card = m →
      (∑ S : Finset (GraphEdge n),
        if 1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤ k
        then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      a * ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤ k ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * a * totalInfluence p f := by sorry
