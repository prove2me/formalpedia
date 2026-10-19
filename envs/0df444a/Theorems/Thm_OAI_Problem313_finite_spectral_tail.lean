-- Prove2me | Theorems.Thm_OAI_Problem313_finite_spectral_tail
-- name    : OAI.Problem313.finite_spectral_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:10:40.371677+00:00
-- url     : https://prove2.me/theorems/4c0d53f4-dac4-4d6f-aa04-c2a9363956c0
-- title:
--   Markov's inequality for a spectral tail
-- statement:
--   Let $s$ be a finite index set with nonnegative masses $m_i$ and nonnegative degrees $d_i$, and let $K>0$. Then
--   $$
--   \sum_{i\in s:\ d_i>K}m_i\le\frac1K\sum_{i\in s}d_i\,m_i .
--   $$
--
--   Fourier mass on large supports is controlled by the first spectral moment, i.e. by total influence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/SpectralBounds.lean#L11-L31

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

theorem OAI.Problem313.finite_spectral_tail {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i) :
    (∑ i ∈ s with cutoff < degree i, mass i) ≤
      (∑ i ∈ s, degree i * mass i) / cutoff := by sorry
