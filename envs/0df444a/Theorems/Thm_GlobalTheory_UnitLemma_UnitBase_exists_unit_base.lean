-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnitBase_exists_unit_base
-- name    : GlobalTheory.UnitLemma.UnitBase.exists_unit_base
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:34:35.95951+00:00
-- url     : https://prove2.me/theorems/38212252-d0d5-4ba2-a1e5-6a468c217f7f
-- title:
--   Unit Base: exists unit base
-- statement:
--   The Unit Base construction uses the exists unit base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L168-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L168-L212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.UnitBase.exists_unit_base : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      (β₀ : B.A) ∈ Algebra.adjoin K.O {B.g} ∧ ((β₀⁻¹ : B.Aˣ) : B.A) ∈ Algebra.adjoin K.O {B.g} := by sorry
