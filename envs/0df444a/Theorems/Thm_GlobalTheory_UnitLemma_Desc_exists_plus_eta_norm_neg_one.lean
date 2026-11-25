-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_exists_plus_eta_norm_neg_one
-- name    : GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:28.027845+00:00
-- url     : https://prove2.me/theorems/dbfe9d60-0f1d-4f9e-854a-ba58c5c0dd40
-- title:
--   Desc: exists plus eta norm neg one
-- statement:
--   The Desc construction uses the exists plus eta norm neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPlusElementEtaNormNegOne.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPlusElementEtaNormNegOne.lean#L15-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPlusElementEtaNormNegOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one : ∀ (K : UQ) (B : InvAlg K) (f : B.A), IsIdempotentElem f → f ≠ 0 →
    (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) → B.σ f = f →
    ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by sorry
