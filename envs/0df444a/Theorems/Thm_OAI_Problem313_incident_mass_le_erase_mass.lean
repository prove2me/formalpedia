-- Prove2me | Theorems.Thm_OAI_Problem313_incident_mass_le_erase_mass
-- name    : OAI.Problem313.incident_mass_le_erase_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:33:43.239123+00:00
-- url     : https://prove2.me/theorems/89e9da2e-17cd-4515-86e4-d3736de032b5
-- title:
--   Supports through a coordinate inject into derivative supports
-- statement:
--   Let $\iota$ be finite, $i\in\iota$, $b\ge0$ on subsets, $C\ge0$, and suppose $a_S=C\,b_{S\setminus\{i\}}$ whenever $i\in S$. Then for every $k$,
--   $$
--   \sum_{S\ni i,\ |S|\le k}a_S\le C\sum_{|T|\le k}b_T .
--   $$
--
--   With $a$ the squared Fourier coefficients of $f$ and $b$ those of $\Delta_if$, this bounds the mass through $i$ by the low-level mass of the derivative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/LowDegreeBounds.lean#L73-L111

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
open Finset

theorem OAI.Problem313.incident_mass_le_erase_mass
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a b : Finset ι → ℝ) (hb : ∀ T, 0 ≤ b T) (i : ι) (k C : ℝ)
    (hC : 0 ≤ C)
    (hderiv : ∀ S, i ∈ S → a S = C * b (S.erase i)) :
    (∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      C * ∑ T : Finset ι, if (T.card : ℝ) ≤ k then b T else 0 := by sorry
