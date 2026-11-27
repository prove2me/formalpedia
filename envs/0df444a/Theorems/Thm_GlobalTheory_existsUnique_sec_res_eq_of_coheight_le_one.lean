-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_sec_res_eq_of_coheight_le_one
-- name    : GlobalTheory.existsUnique_sec_res_eq_of_coheight_le_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:15.016648+00:00
-- url     : https://prove2.me/theorems/46336e01-cd2c-41c1-9244-3e1a000e1161
-- title:
--   Global Theory: exists Unique sec res eq of coheight le one
-- statement:
--   The Global Theory construction uses the exists Unique sec res eq of coheight le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L439-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L439-L455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}}

theorem GlobalTheory.existsUnique_sec_res_eq_of_coheight_le_one [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (L : LB X) {U : X.Opens} (hU : ∀ x : X, Order.coheight x ≤ 1 → x ∈ U)
    {s : ∀ i, Γ(X, U ⊓ L.U i)} (hs : s ∈ secOn L U) :
    ∃! t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i := by sorry
