-- Prove2me | Theorems.Thm_OAI_Problem313_unitQuantile_mem_Ioo
-- name    : OAI.Problem313.unitQuantile_mem_Ioo
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:51:57.692741+00:00
-- url     : https://prove2.me/theorems/377f6077-b7ed-4213-9db5-91b5e6281c91
-- title:
--   Quantiles of a continuous distribution function lie strictly inside
-- statement:
--   Let $\mu:\mathbb{R}\to\mathbb{R}$ be continuous with $\mu(0)=0$ and $\mu(1)=1$, and $0<a<1$. Then the quantile $q_\mu(a)=\inf\{p\in[0,1]:a\le\mu(p)\}$ satisfies
--   $$
--   0<q_\mu(a)<1 .
--   $$
--
--   For a nontrivial increasing graph property, the threshold densities $q(\varepsilon)$ and $q(1-\varepsilon)$ are interior points of $[0,1]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/Quantile.lean#L42-L56

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

theorem OAI.Problem313.unitQuantile_mem_Ioo {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    unitQuantile μ a ∈ Set.Ioo (0 : ℝ) 1 := by sorry
