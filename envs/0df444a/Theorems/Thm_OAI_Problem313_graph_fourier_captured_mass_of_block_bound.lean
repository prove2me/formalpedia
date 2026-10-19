-- Prove2me | Theorems.Thm_OAI_Problem313_graph_fourier_captured_mass_of_block_bound
-- name    : OAI.Problem313.graph_fourier_captured_mass_of_block_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:50:34.607873+00:00
-- url     : https://prove2.me/theorems/6921cfeb-ff0b-4a73-a334-2f43233dcf02
-- title:
--   Square-root blocks capture the low Fourier levels
-- statement:
--   For a graph property $f$ on $n$ labelled vertices and $0<p<1$, let $\hat f(S)$ be the $p$-biased Fourier coefficients of $[f]$ over edge sets $S$, $I_e^p(f)$ the probability that edge $e$ is pivotal, and $I^p(f)=\sum_eI_e^p(f)$. An edge touches a vertex block $B$ if it has an endpoint in $B$. Let $n\ge2$ with $\log n\ge16$, $m=\lfloor\sqrt n\rfloor$, $\sigma=\sqrt{p(1-p)}$ and $k=\sigma\log m/64$. Assume every block $B$ of $m$ vertices satisfies
--   $$
--   \sum_{S:\ 1\le|S\cap\text{touch}(B)|\le k}\hat f(S)^2\le m^{-1/4}\sum_{e\text{ touches }B}I_e^p(f) .
--   $$
--   Then $\sum_{S\ne\emptyset,|S|\le k^2/2}\hat f(S)^2\le4m^{-1/4}I^p(f)$.
--
--   At the square-root block size all counting and numerical premises are discharged. Only the fixed-block analytic estimate remains as an input.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/GraphBlockAverage.lean#L92-L128

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

theorem OAI.Problem313.graph_fourier_captured_mass_of_block_bound
    {n : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hn : 2 ≤ n) (ht : 16 ≤ Real.log (n : ℝ))
    (hp : 0 < p) (hp1 : p < 1)
    (hblock : ∀ B : Finset (Fin n), B.card = ⌊Real.sqrt (n : ℝ)⌋₊ →
      (∑ S : Finset (GraphEdge n),
        if 1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤
              Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64
        then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤
          (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) * totalInfluence p f := by sorry
