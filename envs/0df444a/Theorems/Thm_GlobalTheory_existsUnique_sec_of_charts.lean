-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_sec_of_charts
-- name    : GlobalTheory.existsUnique_sec_of_charts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:09.135744+00:00
-- url     : https://prove2.me/theorems/90521050-863e-49bf-bc71-730c20d3e713
-- title:
--   Global Theory: exists Unique sec of charts
-- statement:
--   The Global Theory construction uses the exists Unique sec of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L205-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L205-L227

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

theorem GlobalTheory.existsUnique_sec_of_charts (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom)
    {L : LB X} {L' : LB Y} (e : L'.ι ≃ L.ι) (hU : ∀ j, L'.U j = f ⁻¹ᵁ L.U (e j))
    (hg : ∀ i j, (L'.g i j).val = (f.appLE (L.U (e i) ⊓ L.U (e j)) (L'.U i ⊓ L'.U j)
      (inf_le_inf (hU i).le (hU j).le)).hom (L.g (e i) (e j)).val) (s : L'.Sec) :
    ∃! t : L.Sec, ∀ j, (f.appLE (L.U (e j)) (L'.U j) (hU j).le).hom (t.f (e j)) = s.f j := by sorry
