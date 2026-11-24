-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeckeId_count_pole
-- name    : GlobalTheory.SW.HeckeId.count_pole
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:40:00.402011+00:00
-- url     : https://prove2.me/theorems/14a18225-3bcf-4be4-a82c-12cfe01cbc6d
-- title:
--   Hecke Id: count pole
-- statement:
--   The Hecke Id construction uses the count pole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L461-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L461-L483

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem GlobalTheory.SW.HeckeId.count_pole {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) {a b : 𝓞 E} (ha : a ∈ P) (hab : a + b = 1)
    (u : X →ₗ[𝓞 E] (Fin n → E)) (hu : ¬ ∀ ξ, u ξ ∈ Λ) {A : ℕ} (B : Fin A → Submodule (𝓞 E) X)
    (hB : ∀ i, B i ∈ Hyp (conjI P) X) (hB1 : Function.Injective B)
    (hB2 : ∀ K ∈ Hyp (conjI P) X, ∃ i, B i = K) (η : Fin A → X) (hη : ∀ i, η i ∉ B i) :
    {i | (∀ ξ ∈ B i, u ξ ∈ Λ) ∧ ∀ ξ, Int' (u (η i)) (u (b • ξ))}.ncard =
      {Λ' ∈ Nb M P Λ | ∀ ξ, u ξ ∈ Λ'}.ncard := by sorry
