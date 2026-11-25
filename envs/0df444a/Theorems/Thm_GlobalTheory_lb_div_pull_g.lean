-- Prove2me | Theorems.Thm_GlobalTheory_lb_div_pull_g
-- name    : GlobalTheory.lb_div_pull_g
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:14.627054+00:00
-- url     : https://prove2.me/theorems/408d667d-2661-4b75-b607-617f52e83c9e
-- title:
--   Global Theory: lb div pull g
-- statement:
--   The Global Theory construction uses the lb div pull g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L321-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L321-L345

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

theorem GlobalTheory.lb_div_pull_g (L M : LB X) (f : Y ⟶ X)
    (p q : (PUnit.{u + 1} → M.ι) × (PUnit.{u + 1} → L.ι)) :
    ((M.pull f).div (L.pull f)).g p q =
      res (inf_le_inf (lb_div_pull_U L M f p).le (lb_div_pull_U L M f q).le)
        (pullU f ((M.div L).U (p.1 PUnit.unit, p.2 PUnit.unit) ⊓
            (M.div L).U (q.1 PUnit.unit, q.2 PUnit.unit))
          ((M.div L).g (p.1 PUnit.unit, p.2 PUnit.unit) (q.1 PUnit.unit, q.2 PUnit.unit))) := by sorry
