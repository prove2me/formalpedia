-- Prove2me | Theorems.Thm_OAI_Problem313_variance_from_fourier_capture
-- name    : OAI.Problem313.variance_from_fourier_capture
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:11:18.564344+00:00
-- url     : https://prove2.me/theorems/b4870dfd-6aa0-458b-a90a-e2aa1131cec7
-- title:
--   Variance bound from capturing the low Fourier levels
-- statement:
--   Let $\iota$ be finite and $(c_S)_{S\subseteq\iota}$ real numbers, with $\mathrm{Var}=\sum_{S\ne\emptyset}c_S^2$ and $\sum_S|S|\,c_S^2=\sigma^2I$. Let $\sigma,\ell>0$ and $L\in\mathbb{R}$, and suppose the low part satisfies
--   $$
--   \sum_{S\ne\emptyset,\ |S|\le(\sigma\ell/64)^2/2}c_S^2\le L\cdot I .
--   $$
--   Then $\mathrm{Var}\le\bigl(L+8192/\ell^2\bigr)I$.
--
--   The variance splits into low levels, handled by a capture argument, and high levels, handled by Markov's inequality applied to the influence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/SpectralBounds.lean#L131-L155

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

theorem OAI.Problem313.variance_from_fourier_capture {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma ell influence lowConstant : ℝ)
    (hsigma : 0 < sigma) (hell : 0 < ell)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * ell / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ lowConstant * influence) :
    variance ≤ (lowConstant + 8192 / ell ^ 2) * influence := by sorry
