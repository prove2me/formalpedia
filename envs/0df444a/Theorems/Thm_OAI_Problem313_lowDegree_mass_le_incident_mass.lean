-- Prove2me | Theorems.Thm_OAI_Problem313_lowDegree_mass_le_incident_mass
-- name    : OAI.Problem313.lowDegree_mass_le_incident_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:33:04.448997+00:00
-- url     : https://prove2.me/theorems/04e695dc-d1ef-49a9-abe3-43687735ac1a
-- title:
--   Low-level mass is covered by coordinate-incident masses
-- statement:
--   Let $\iota$ be finite, $a\ge0$ on subsets of $\iota$, and $k\in\mathbb{R}$. Then
--   $$
--   \sum_{S\ne\emptyset,\ |S|\le k}a_S\le\sum_{i\in\iota}\ \sum_{S\ni i,\ |S|\le k}a_S .
--   $$
--
--   Each nonempty support is counted at least once by one of its coordinates. This reduces the low-level mass to per-coordinate quantities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/LowDegreeBounds.lean#L14-L42

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

theorem OAI.Problem313.lowDegree_mass_le_incident_mass
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (ha : ∀ S, 0 ≤ a S) (k : ℝ) :
    (∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      ∑ i : ι, ∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 := by sorry
