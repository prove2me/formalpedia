-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_secOn_of_pull
-- name    : GlobalTheory.existsUnique_secOn_of_pull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:44:40.851721+00:00
-- url     : https://prove2.me/theorems/f2353871-c272-4ae5-8b97-19846af099e8
-- title:
--   Global Theory: exists Unique sec On of pull
-- statement:
--   The Global Theory construction uses the exists Unique sec On of pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L578-L594
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L578-L594

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

theorem GlobalTheory.existsUnique_secOn_of_pull (L : LB X) (W : X.Opens) (r : (L.pull W.ι).Sec) :
    ∃! s : ∀ i, Γ(X, W ⊓ L.U i), s ∈ secOn L W ∧ ∀ j : PUnit.{1} → L.ι,
      (W.ι.appLE (W ⊓ L.U (j PUnit.unit)) _ (lb_pull_ι_U L W j).le).hom (s (j PUnit.unit)) =
        r.f j := by sorry
