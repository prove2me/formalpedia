-- Prove2me | Theorems.Thm_OAI_Problem313_graphQuantile_width_of_variance_bound
-- name    : OAI.Problem313.graphQuantile_width_of_variance_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:54:00.413299+00:00
-- url     : https://prove2.me/theorems/0d42680d-d24f-4292-ac53-e1d22ad5ebf9
-- title:
--   Threshold width from a variance–influence inequality
-- statement:
--   For a graph property $f$ on $n$ labelled vertices and $0<p<1$, let $\hat f(S)$ be the $p$-biased Fourier coefficients of $[f]$ over edge sets $S$, $I_e^p(f)$ the probability that edge $e$ is pivotal, and $I^p(f)=\sum_eI_e^p(f)$. An edge touches a vertex block $B$ if it has an endpoint in $B$. Let $f$ be increasing and nontrivial, $C\ge0$ and $0<\varepsilon<\frac12$, and suppose $\mathrm{Var}_p(f)\le C\,I^p(f)$ for all $p\in(0,1)$. With $q(a)=\inf\{p\in[0,1]:\mu_p(f)\ge a\}$,
--   $$
--   q(1-\varepsilon)-q(\varepsilon)\le4C\log\frac1{2\varepsilon} .
--   $$
--
--   This is the analytic deduction from the variance bound to the sharp threshold. The rest of the proof only has to establish the variance bound with $C=2^{17}/(\log n)^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/SharpThreshold.lean#L12-L49

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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Quantile

open OAI OAI.Problem313

theorem OAI.Problem313.graphQuantile_width_of_variance_bound {n : ℕ} {f : GraphConfig n → Bool}
    {C ε : ℝ} (hC : 0 ≤ C)
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (hvariance : ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      graphVariance p f ≤ C * totalInfluence p f) :
    graphQuantile (1 - ε) f - graphQuantile ε f ≤
      (4 * C) * Real.log (1 / (2 * ε)) := by sorry
