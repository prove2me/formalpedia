-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_secOn_of_coheight_le_one
-- name    : GlobalTheory.existsUnique_secOn_of_coheight_le_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:38.511543+00:00
-- url     : https://prove2.me/theorems/e3bcd638-d92b-4777-8198-725194347fdb
-- title:
--   Global Theory: exists Unique sec On of coheight le one
-- statement:
--   The Global Theory construction uses the exists Unique sec On of coheight le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L422-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L422-L437

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

theorem GlobalTheory.existsUnique_secOn_of_coheight_le_one [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (L : LB X) {V W : X.Opens} (h : W ≤ V) (hW : ∀ x ∈ V, Order.coheight x ≤ 1 → x ∈ W)
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) :
    ∃! t : ∀ i, Γ(X, V ⊓ L.U i),
      t ∈ secOn L V ∧ ∀ i, resG X (inf_le_inf_right _ h) (t i) = s i := by sorry
