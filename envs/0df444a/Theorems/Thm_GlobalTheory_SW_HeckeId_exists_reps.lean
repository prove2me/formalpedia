-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeckeId_exists_reps
-- name    : GlobalTheory.SW.HeckeId.exists_reps
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:40:46.670205+00:00
-- url     : https://prove2.me/theorems/f5227257-9edd-41b6-ab50-6e93e3991b16
-- title:
--   Hecke Id: exists reps
-- statement:
--   The Hecke Id construction uses the exists reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L154-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L154-L183

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
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
attribute [local instance] Ideal.Quotient.field

theorem GlobalTheory.SW.HeckeId.exists_reps [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] {B : ℕ}
    (hB : Nat.card (O ⧸ P) ^ Module.finrank O M = B) : ∃ ξ : Fin B → M, ∀ χ : AddChar M ℂ,
    (∀ c ∈ P, ∀ x, χ (c • x) = 1) → ∑ j, χ (ξ j) = if ∀ x, χ x = 1 then (B : ℂ) else 0 := by sorry
