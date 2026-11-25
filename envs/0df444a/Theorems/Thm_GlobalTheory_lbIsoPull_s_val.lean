-- Prove2me | Theorems.Thm_GlobalTheory_lbIsoPull_s_val
-- name    : GlobalTheory.lbIsoPull_s_val
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:12.031796+00:00
-- url     : https://prove2.me/theorems/eed908ea-fa96-4712-ab8b-26e6e09620e1
-- title:
--   Global Theory: lb Iso Pull s val
-- statement:
--   The Global Theory construction uses the lb Iso Pull s val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L347-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L347-L353

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
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y : Scheme.{u}}

theorem GlobalTheory.lbIsoPull_s_val {L M : LB X} (w : LB.Iso L M) (f : Y ⟶ X)
    (p : (PUnit.{u + 1} → M.ι) × (PUnit.{u + 1} → L.ι)) :
    ((lbIsoPull w f).s p).val =
      (f.appLE ((M.div L).U (p.1 PUnit.unit, p.2 PUnit.unit)) (((M.pull f).div (L.pull f)).U p)
        (lb_div_pull_U L M f p).le).hom (w.s (p.1 PUnit.unit, p.2 PUnit.unit)).val := by sorry
