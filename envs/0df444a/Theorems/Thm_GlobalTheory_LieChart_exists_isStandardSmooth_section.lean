-- Prove2me | Theorems.Thm_GlobalTheory_LieChart_exists_isStandardSmooth_section
-- name    : GlobalTheory.LieChart.exists_isStandardSmooth_section
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:48:53.51907+00:00
-- url     : https://prove2.me/theorems/fbc595df-9811-4378-b835-98736c9e4f3f
-- title:
--   Lie Chart: exists is Standard Smooth section
-- statement:
--   The Lie Chart construction uses the exists is Standard Smooth section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L190-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L190-L209

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAffineLieBasisBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieChart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj

theorem GlobalTheory.LieChart.exists_isStandardSmooth_section {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)
    (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V) (e : V ≤ p ⁻¹ᵁ U),
      x ∈ U ∧ U ≤ W ∧ U ≤ s ⁻¹ᵁ V ∧ (p.appLE U V e).hom.IsStandardSmooth := by sorry
