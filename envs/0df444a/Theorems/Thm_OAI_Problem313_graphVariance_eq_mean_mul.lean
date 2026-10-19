-- Prove2me | Theorems.Thm_OAI_Problem313_graphVariance_eq_mean_mul
-- name    : OAI.Problem313.graphVariance_eq_mean_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:05:00.043817+00:00
-- url     : https://prove2.me/theorems/e7061817-5048-4e08-a3de-e8813dd550d9
-- title:
--   The variance of a graph property is $\mu(1-\mu)$
-- statement:
--   For a graph property $f$ on $n$ vertices and any $p$, let $\mu=\mu_p(f)=\sum_xw_p(x)[f(x)]$, where $w_p$ is the $p$-biased weight. Then
--   $$
--   \mathrm{Var}_p(f)=\sum_xw_p(x)\bigl([f(x)]-\mu\bigr)^2=\mu(1-\mu) .
--   $$
--
--   The variance is large exactly when $\mu$ is away from $0$ and $1$, i.e. inside the threshold window.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/Probability.lean#L60-L76

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

open OAI OAI.Problem313

theorem OAI.Problem313.graphVariance_eq_mean_mul {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    graphVariance p f = graphMean p f * (1 - graphMean p f) := by sorry
