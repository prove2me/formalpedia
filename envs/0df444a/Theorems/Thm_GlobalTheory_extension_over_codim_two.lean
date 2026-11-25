-- Prove2me | Theorems.Thm_GlobalTheory_extension_over_codim_two
-- name    : GlobalTheory.extension_over_codim_two
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:40.047961+00:00
-- url     : https://prove2.me/theorems/40bc0a09-7904-553c-a4db-340ad62cc702
-- title:
--   Global Theory: extension over codim two
-- statement:
--   The Global Theory construction uses the extension over codim two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L650-L691
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L650-L691

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.extension_over_codim_two (X : Scheme.{0}) [IsLocallyNoetherian X]
    (hX : Geo.Tor.IsNormalScheme X) :
    (∀ U : X.Opens, (∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U) →
      (∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ U ≤ V))) ∧
      (∀ (L : LB X) (r : (L.pull U.ι).Sec), ∃! t : L.Sec, lbSecPull L t U.ι = r) ∧
      (∀ (L : LB X) (V : X.Opens), ∀ s ∈ secOn L (V ⊓ U), ∃! t : ∀ i, Γ(X, V ⊓ L.U i),
        t ∈ secOn L V ∧ ∀ i, resG X (inf_le_inf_right _ inf_le_left) (t i) = s i) ∧
      (∀ (L : LB X) (r : (L.pull U.ι).Gen), r.IsGen →
        ∃! t : L.Gen, t.IsGen ∧ L.genPull t U.ι = r) ∧
      (∀ (L M : LB X) (w : LB.Iso (L.pull U.ι) (M.pull U.ι)), w.IsGen →
        ∃! v : LB.Iso L M, v.IsGen ∧
          LB.linCombIso v (K := PUnit) (fun _ ↦ U.ι) (fun _ ↦ 1) = w) ∧
      (∀ L M : LB X, LBIso (L.pull U.ι) (M.pull U.ι) ↔ LBIso L M)) ∧
    (∀ x : X, Order.coheight x = 1 →
      ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x)) ∧
    (∀ [IsIntegral X] (L : LB X), L.IsLB → ∀ (W : X.Opens) [Nonempty W],
      (∀ s ∈ secOn L W, (∃! t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i) ↔
        ∀ x : X, Order.coheight x = 1 → x ∉ W →
          ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)), x ∈ L.U i ∧
            X.germToFunctionField (W ⊓ L.U i) (s i) ∈
              (algebraMap (X.presheaf.stalk x) X.functionField).range) ∧
      (∀ r : (L.pull W.ι).Sec, (∃ t : L.Sec, lbSecPull L t W.ι = r) ↔
        ∀ x : X, Order.coheight x = 1 → x ∉ W →
          ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)) (a : Γ(X, W ⊓ L.U i)), x ∈ L.U i ∧
            (W.ι.appLE (W ⊓ L.U i) _ (lb_pull_ι_U L W fun _ ↦ i).le).hom a = r.f (fun _ ↦ i) ∧
            X.germToFunctionField (W ⊓ L.U i) a ∈
              (algebraMap (X.presheaf.stalk x) X.functionField).range)) := by sorry
