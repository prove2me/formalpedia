-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_charpoly_overExt_separable
-- name    : GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:35:42.346257+00:00
-- url     : https://prove2.me/theorems/93cf83af-f3aa-4c2f-ac47-5168099c3ee9
-- title:
--   Unr: charpoly over Ext separable
-- statement:
--   The Unr construction uses the charpoly over Ext separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeparableCharpolyInvAlgBaseChangeUnramified.lean#L11-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeparableCharpolyInvAlgBaseChangeUnramified.lean#L11-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), B.P.Separable → (overExt φ B ψ hψ hσ).P.Separable := by sorry
