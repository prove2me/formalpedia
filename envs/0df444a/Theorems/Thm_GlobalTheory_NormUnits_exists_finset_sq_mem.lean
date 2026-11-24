-- Prove2me | Theorems.Thm_GlobalTheory_NormUnits_exists_finset_sq_mem
-- name    : GlobalTheory.NormUnits.exists_finset_sq_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:18.665509+00:00
-- url     : https://prove2.me/theorems/acd25407-e23d-4548-8b7b-0988daad128e
-- title:
--   Norm Units: exists finset sq mem
-- statement:
--   The Norm Units construction uses the exists finset sq mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinsetCosetsIntegralNormUnits.lean#L15-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinsetCosetsIntegralNormUnits.lean#L15-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetCosetsIntegralNormUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.NormUnits

theorem GlobalTheory.NormUnits.exists_finset_sq_mem {G : Type} [CommGroup G] (N : Subgroup G) (hN : Group.FG (G ⧸ N)) :
    ∃ F : Finset G, ∀ u : G, u ^ 2 ∈ N → ∃ f ∈ F, u * f⁻¹ ∈ N := by sorry
