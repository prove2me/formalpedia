-- Prove2me | Theorems.Thm_GlobalTheory_exists_resG_eq_of_secOn
-- name    : GlobalTheory.exists_resG_eq_of_secOn
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:04.957804+00:00
-- url     : https://prove2.me/theorems/6da150ee-67b6-42ce-b833-d11c664bab75
-- title:
--   Global Theory: exists res G eq of sec On
-- statement:
--   The Global Theory construction uses the exists res G eq of sec On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L490-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L490-L508

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

theorem GlobalTheory.exists_resG_eq_of_secOn {L : LB X} {W : X.Opens} [Nonempty W]
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) (i : L.ι) {O : X.Opens} (h : W ⊓ L.U i ≤ O)
    (hO : O ≤ L.U i)
    (H : ∀ x ∈ O, Order.coheight x = 1 → x ∉ W → ∃ (j : L.ι) (_ : Nonempty (W ⊓ L.U j : X.Opens)),
      x ∈ L.U j ∧ X.germToFunctionField (W ⊓ L.U j) (s j) ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ t : Γ(X, O), resG X h t = s i := by sorry
