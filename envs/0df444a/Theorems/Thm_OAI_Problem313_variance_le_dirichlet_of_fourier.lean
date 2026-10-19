-- Prove2me | Theorems.Thm_OAI_Problem313_variance_le_dirichlet_of_fourier
-- name    : OAI.Problem313.variance_le_dirichlet_of_fourier
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:11:51.189467+00:00
-- url     : https://prove2.me/theorems/e0f3d98e-95d5-4b3b-ae3c-6436c0e19f2a
-- title:
--   The Poincaré inequality from Parseval
-- statement:
--   Let $\iota$ be finite and $(c_S)_{S\subseteq\iota}$ real numbers. If $\mathrm{Var}=\sum_{S\ne\emptyset}c_S^2$ and $\mathcal{E}=\sum_S|S|\,c_S^2$, then
--   $$
--   \mathrm{Var}\le\mathcal{E} .
--   $$
--
--   For Boolean functions this is the Poincaré inequality $\mathrm{Var}_p(f)\le p(1-p)I^p(f)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/SpectralBounds.lean#L157-L176

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

theorem OAI.Problem313.variance_le_dirichlet_of_fourier {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance dirichlet : ℝ)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = dirichlet) :
    variance ≤ dirichlet := by sorry
