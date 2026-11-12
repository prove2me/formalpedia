-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_exists_forcedSupportedCertificateFamily
-- name    : OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_forcedSupportedCertificateFamily
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:17:11.606208+00:00
-- url     : https://prove2.me/theorems/f67dee16-3906-4178-a73c-114e264c4471
-- title:
--   OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_forcedSupportedCertificateFamily: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_forcedSupportedCertificateFamily` of [lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundMainFinalEnumeratedCertificateFamilies.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundMainFinalEnumeratedCertificateFamilies.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment`, with `open SetFormula SetRealization`):
--
--   ```lean
--   theorem exists_forcedSupportedCertificateFamily
--       (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
--       (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
--       (smallD : M.groundEmbeddable D ZFSet.omega)
--       (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
--       let geometry := run.finalGeometry i₀
--       letI := geometry.group_code.toGroup
--       letI := geometry.meet.order.toPartialOrder
--       letI := geometry.decodedBottom
--       let b := SetMembers.presentation geometry.carrier
--       let t := SetMembers.presentation geometry.actors
--       let d := geometry.decodedAction
--       let directed := geometry.decoded_directed fulfilled.directed
--       ∀ (a : PosetAction (SetMembers geometry.actors) Q)
--         (_maps : a.conditionMapFamily s t ∈ M.sets)
--         (T : ZFSet.{u}) (_hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
--         (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
--         (_children : ∀ τ : Name s, τ.val ∈ T →
--           HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
--         (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
--         (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
--         (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
--           d.principalFix v ≤ a.stabilizer s x.val →
--           d.principalFix w ≤ a.stabilizer s y.val →
--           HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
--           HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
--           Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
--           ∃ τ : (M.nameDomain s).names,
--             HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
--             d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
--             Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
--         (J : ZFSet.{u}) (_hJ : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
--         (_smallJ : M.groundEmbeddable J ZFSet.omega)
--         (_hs : ∀ z : Name s, z.val ∈ J →
--           HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z)
--         (_subset : ∀ z : Name s, z.val ∈ J → Name.eval {p | H.mem p} z ⊆
--           Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
--         (p : Q) (_hp : H.mem p),
--         ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
--           ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
--             (M.niceSupportNameCodes a s T d.principalFix)) k ∧
--           k ⊆ M.supportedCertificateFamilyRelation a s b T d.principalFix
--             geometry.order J validJ H ∧
--           ∃ q, H.mem q ∧ q ≤ p ∧
--             Forces (M.nameDomain s) supportedCertificateFamilyFormula
--               (M.supportedCertificateFamilyEnv a s t b T d.principalFix pairing unions powers
--                 separation collection carrier geometry.actors_ground geometry.carrier_ground
--                 (geometry.decoded_supportBasis_ground pairing unions powers separation)
--                 _maps _hT valid (M.omega_mem separation infinite) geometry.order J k
--                 geometry.order_ground _hJ hk validJ) q ∧
--             ∀ (z : (M.nameDomain s).names) (F B f : ZFSet.{u}),
--               ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
--               F = M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∧
--               MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
--               B.Nonempty ∧ M.DecidesVisibilityProfile a s b d.principalFix T F z.val q ∧
--               (∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
--                 ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) ∧
--               ∃ e ∈ M.sets, ∃ names ∈ M.sets,
--                 ZFSet.IsFunc ZFSet.omega B e ∧
--                 ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes a s T d.principalFix) names ∧
--                 (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
--                 (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
--                   ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
--                 (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
--                   ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.MeetFilterCode`, `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.GroupCode.toGroup`, `OAI.PartitionPilot.Forcing.MeetOrderCode`, `OAI.PartitionPilot.Forcing.PartialOrderCode.toPartialOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.omega_mem` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.ConditionFilter` and `OAI.PartitionPilot.Forcing.ConditionFilter.GenericFor` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.MeetOrderCode.smallMeet`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry`, `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.InternallyCountablyClosed`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedBottom`, `OAI.PartitionPilot.Forcing.Name.ForcesEq`, `OAI.PartitionPilot.Forcing.Name.eval`, `OAI.PartitionPilot.Forcing.Name.familySet`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.PosetAction.stabilizer`, `OAI.PartitionPilot.Forcing.SetFormula.Forces`, `OAI.PartitionPilot.Forcing.SetFormula.formulaFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.DecidesVisibilityProfile`, `OAI.PartitionPilot.Forcing.TransitiveGround.codedFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.Forcing.TransitiveGround.niceSupportNameCodes` and `OAI.PartitionPilot.Forcing.Name.NameDomain` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.supportedCertificateFamilyFormula`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedAction`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_supportBasis_ground`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily` and `OAI.PartitionPilot.Forcing.TransitiveGround.visibleSupportProfile` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, `OAI.PartitionPilot.Forcing.GroundMainPrefix` and `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_directed` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.supportedEqualityCertificateBound` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.supportedCertificateFamilyRelation` (definitions bundle `OAIQ253P008` of this split); `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalGeometry` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.supportedCertificateFamilyEnv` (definitions bundle `OAIQ253P011` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundEmbeddable` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proofs of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.augmented_profile_family` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch` of this split import it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundMainFinalEnumeratedCertificateFamilies.lean (declaration OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_forcedSupportedCertificateFamily)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {Q : Type u} [PartialOrder Q] [OrderTop Q] (s : Presentation Q)

theorem exists_forcedSupportedCertificateFamily
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (_maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (_hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (J : ZFSet.{u}) (_hJ : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
      (_smallJ : M.groundEmbeddable J ZFSet.omega)
      (_hs : ∀ z : Name s, z.val ∈ J →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z)
      (_subset : ∀ z : Name s, z.val ∈ J → Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (p : Q) (_hp : H.mem p),
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes a s T d.principalFix)) k ∧
        k ⊆ M.supportedCertificateFamilyRelation a s b T d.principalFix
          geometry.order J validJ H ∧
        ∃ q, H.mem q ∧ q ≤ p ∧
          Forces (M.nameDomain s) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv a s t b T d.principalFix pairing unions powers
              separation collection carrier geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              _maps _hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground _hJ hk validJ) q ∧
          ∀ (z : (M.nameDomain s).names) (F B f : ZFSet.{u}),
            ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
            F = M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∧
            MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
            B.Nonempty ∧ M.DecidesVisibilityProfile a s b d.principalFix T F z.val q ∧
            (∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
              ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) ∧
            ∃ e ∈ M.sets, ∃ names ∈ M.sets,
              ZFSet.IsFunc ZFSet.omega B e ∧
              ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes a s T d.principalFix) names ∧
              (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
              (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
              (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  sorry

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end
