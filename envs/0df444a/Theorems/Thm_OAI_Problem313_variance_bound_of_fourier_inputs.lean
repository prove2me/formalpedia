-- Prove2me | Theorems.Thm_OAI_Problem313_variance_bound_of_fourier_inputs
-- name    : OAI.Problem313.variance_bound_of_fourier_inputs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:13:47.41186+00:00
-- url     : https://prove2.me/theorems/153f9f6f-3eee-4f98-b7df-6569bf3fe75d
-- title:
--   Variance at most $2^{17}I/t^2$ given low-level capture
-- statement:
--   Let $\iota$ be finite and $(c_S)_{S\subseteq\iota}$ real numbers, with $\mathrm{Var}=\sum_{S\ne\emptyset}c_S^2$ and $\sum_S|S|\,c_S^2=\sigma^2I$. Assume $0<\sigma$, $\sigma^2\le\frac14$, $I\ge0$, $t>0$, and that whenever $t\ge16$ there is $m>0$ with $\log m\ge t/3$ and
--   $$
--   \sum_{S\ne\emptyset,\ |S|\le(\sigma\log m/64)^2/2}c_S^2\le4m^{-1/4}I .
--   $$
--   Then $\mathrm{Var}\le\dfrac{2^{17}}{t^2}\,I$.
--
--   With $t=\log n$ this is the Bourgain–Kalai-type bound: variance is at most a $(\log n)^{-2}$ multiple of total influence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/VarianceReduction.lean#L35-L58

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

theorem OAI.Problem313.variance_bound_of_fourier_inputs {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma influence t : ℝ)
    (hsigma : 0 < sigma) (hsigma_sq : sigma ^ 2 ≤ 1 / 4)
    (hinfluence : 0 ≤ influence) (ht : 0 < t)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : 16 ≤ t → ∃ m : ℝ, 0 < m ∧ t / 3 ≤ Real.log m ∧
      (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * Real.log m / 64) ^ 2 / 2, coeff S ^ 2)
        ≤ (4 * m ^ (-1 / 4 : ℝ)) * influence) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by sorry
