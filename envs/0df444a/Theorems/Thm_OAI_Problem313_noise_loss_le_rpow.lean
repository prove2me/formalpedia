-- Prove2me | Theorems.Thm_OAI_Problem313_noise_loss_le_rpow
-- name    : OAI.Problem313.noise_loss_le_rpow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:28:07.99275+00:00
-- url     : https://prove2.me/theorems/5be3175c-968f-4283-8eb6-8a2b61cf6ca0
-- title:
--   The noise loss is at most $m^{1/16}$
-- statement:
--   Let $0<\sigma\le\frac12$, $m\ge1$ and $k=\sigma\log m/64$. Then
--   $$
--   \Bigl(\frac\sigma4\Bigr)^{-2k}\le m^{1/16} .
--   $$
--
--   Undoing noise with parameter $\sigma/4$ on levels up to $k$ costs only a tiny power of $m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/LowDegreeConstants.lean#L38-L54

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

theorem OAI.Problem313.noise_loss_le_rpow {σ m : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m) :
    (σ / 4) ^ (-(2 : ℝ) * (σ * Real.log m / 64)) ≤ m ^ (1 / 16 : ℝ) := by sorry
