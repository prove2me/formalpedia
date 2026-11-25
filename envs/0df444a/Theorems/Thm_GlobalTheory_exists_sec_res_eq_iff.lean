-- Prove2me | Theorems.Thm_GlobalTheory_exists_sec_res_eq_iff
-- name    : GlobalTheory.exists_sec_res_eq_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:29.861293+00:00
-- url     : https://prove2.me/theorems/377d8a27-078b-4815-92ce-ed12c0fda016
-- title:
--   Global Theory: exists sec res eq iff
-- statement:
--   The Global Theory construction uses the exists sec res eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L538-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L538-L558

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
variable [IsIntegral X]
variable [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]

theorem GlobalTheory.exists_sec_res_eq_iff {L : LB X} (hL : L.IsLB) {W : X.Opens} [Nonempty W]
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) :
    (∃ t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i) ↔
      ∀ x : X, Order.coheight x = 1 → x ∉ W →
        ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)), x ∈ L.U i ∧
          X.germToFunctionField (W ⊓ L.U i) (s i) ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by sorry
