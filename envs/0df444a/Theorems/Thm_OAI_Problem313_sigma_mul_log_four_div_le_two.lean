-- Prove2me | Theorems.Thm_OAI_Problem313_sigma_mul_log_four_div_le_two
-- name    : OAI.Problem313.sigma_mul_log_four_div_le_two
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:27:30.04302+00:00
-- url     : https://prove2.me/theorems/0299e84a-3ab6-4652-9114-76711f261011
-- title:
--   A uniform bound on $\sigma\log(4/\sigma)$
-- statement:
--   For every real $\sigma$ with $0<\sigma\le\frac12$,
--   $$
--   \sigma\log\frac4\sigma\le2 .
--   $$
--
--   In the low-degree estimate $\sigma=\sqrt{p(1-p)}$ is the standard deviation of a $p$-biased bit, and the noise parameter is $\sigma/4$. This inequality controls the resulting noise loss uniformly in the bias $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/LowDegreeConstants.lean#L11-L36

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

open OAI OAI.Problem313
universe u

theorem OAI.Problem313.sigma_mul_log_four_div_le_two {σ : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) : σ * Real.log (4 / σ) ≤ 2 := by sorry
