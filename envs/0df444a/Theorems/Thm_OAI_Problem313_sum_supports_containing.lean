-- Prove2me | Theorems.Thm_OAI_Problem313_sum_supports_containing
-- name    : OAI.Problem313.sum_supports_containing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:07:15.306433+00:00
-- url     : https://prove2.me/theorems/01e3be25-e38b-44df-a858-8474df74673e
-- title:
--   Reindexing supports that contain a fixed coordinate
-- statement:
--   Let $\iota$ be finite, $i\in\iota$, and $a$ a real function on subsets of $\iota$. Then
--   $$
--   \sum_{S\ni i}a(S)=\sum_{S\not\ni i}a(S\cup\{i\}) .
--   $$
--
--   Sums over Fourier supports containing $i$ can be rewritten over supports of the derivative $\Delta_i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/DirichletEnergy.lean#L12-L28

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
open Finset
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem OAI.Problem313.sum_supports_containing (i : ι) (a : Finset ι → ℝ) :
    (∑ S : Finset ι, if i ∈ S then a S else 0) =
      ∑ S : Finset ι, if i ∉ S then a (insert i S) else 0 := by sorry
