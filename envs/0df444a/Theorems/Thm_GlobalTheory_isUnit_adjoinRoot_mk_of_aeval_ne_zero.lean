-- Prove2me | Theorems.Thm_GlobalTheory_isUnit_adjoinRoot_mk_of_aeval_ne_zero
-- name    : GlobalTheory.isUnit_adjoinRoot_mk_of_aeval_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:29.243966+00:00
-- url     : https://prove2.me/theorems/4ccfd6c9-0a33-4ee8-9518-4a3a340beb71
-- title:
--   Global Theory: is Unit adjoin Root mk of aeval ne zero
-- statement:
--   The Global Theory construction uses the is Unit adjoin Root mk of aeval ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L280-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L280-L307

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
universe u
variable {B W : Type u} {K : Type*} [CommRing B] [CommRing W] [Field K] [IsLocalRing B]
  [Algebra B W] [Algebra B K] [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
omit [Algebra B W] [CommRing W]

theorem GlobalTheory.isUnit_adjoinRoot_mk_of_aeval_ne_zero {θ : K} (hθ : IsIntegral (ResidueField B) θ)
    {μ : B[X]} (hμm : μ.Monic) (hμ : μ.map (residue B) = minpoly (ResidueField B) θ) {g : B[X]}
    (hg : aeval θ g ≠ 0) : IsUnit (AdjoinRoot.mk μ g) := by sorry
