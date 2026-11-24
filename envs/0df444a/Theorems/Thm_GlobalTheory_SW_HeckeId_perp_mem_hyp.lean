-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeckeId_perp_mem_hyp
-- name    : GlobalTheory.SW.HeckeId.perp_mem_hyp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:40:29.628795+00:00
-- url     : https://prove2.me/theorems/17b4173a-4b2e-4706-ad5e-caa2debdae94
-- title:
--   Hecke Id: perp mem hyp
-- statement:
--   The Hecke Id construction uses the perp mem hyp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L383-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L383-L419

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

theorem GlobalTheory.SW.HeckeId.perp_mem_hyp {P : Ideal (𝓞 E)} [hP : P.IsMaximal] (hP0 : P ≠ ⊥) {Λ : Lt E n} (hS : SD Λ)
    {y : Fin n → E} (hy : y ∉ Λ) (hQ : ∀ c ∈ conjI P, c • y ∈ Λ) : perp Λ y ∈ Hyp P Λ := by sorry
