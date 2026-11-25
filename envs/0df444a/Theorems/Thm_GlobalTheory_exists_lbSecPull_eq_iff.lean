-- Prove2me | Theorems.Thm_GlobalTheory_exists_lbSecPull_eq_iff
-- name    : GlobalTheory.exists_lbSecPull_eq_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:48:02.401239+00:00
-- url     : https://prove2.me/theorems/5e0fff7a-fbbc-435c-b4a9-4d7fa36414ec
-- title:
--   Global Theory: exists lb Sec Pull eq iff
-- statement:
--   The Global Theory construction uses the exists lb Sec Pull eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L596-L618
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L596-L618

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

theorem GlobalTheory.exists_lbSecPull_eq_iff [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    {L : LB X} (hL : L.IsLB) {W : X.Opens} [Nonempty W] (r : (L.pull W.ι).Sec) :
    (∃ t : L.Sec, lbSecPull L t W.ι = r) ↔
      ∀ x : X, Order.coheight x = 1 → x ∉ W →
        ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)) (a : Γ(X, W ⊓ L.U i)), x ∈ L.U i ∧
          (W.ι.appLE (W ⊓ L.U i) _ (lb_pull_ι_U L W fun _ ↦ i).le).hom a = r.f (fun _ ↦ i) ∧
          X.germToFunctionField (W ⊓ L.U i) a ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by sorry
