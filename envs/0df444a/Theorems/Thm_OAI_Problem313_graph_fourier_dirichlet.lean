-- Prove2me | Theorems.Thm_OAI_Problem313_graph_fourier_dirichlet
-- name    : OAI.Problem313.graph_fourier_dirichlet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:09:07.611042+00:00
-- url     : https://prove2.me/theorems/bde6d361-c5c7-41cb-9479-5e23f9b9aaeb
-- title:
--   Total influence as the first spectral moment
-- statement:
--   For a graph property $f$ on $n$ labelled vertices and $0<p<1$, let $\hat f(S)$ denote the $p$-biased Fourier coefficients of $[f]$ indexed by edge sets $S$, $I^p(f)=\sum_eI_e^p(f)$ the total influence, where $I_e^p(f)$ is the probability that edge $e$ is pivotal, and $\mu_p(f)$ the probability that $f$ holds. Then
--   $$
--   \sum_{S}|S|\,\hat f(S)^2=p(1-p)\,I^p(f) .
--   $$
--
--   This is the biased Fourier formula for total influence. Small influence means the Fourier mass sits on small edge sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierDirichlet.lean#L79-L97

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

open OAI OAI.Problem313
universe u

theorem OAI.Problem313.graph_fourier_dirichlet {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : GraphConfig n → Bool) :
    (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
      (BiasedFourier.coeff p (fun x => boolReal (f x)) S)^2) =
      p * (1 - p) * totalInfluence p f := by sorry
