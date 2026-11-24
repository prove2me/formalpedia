-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_exists_key
-- name    : GlobalTheory.UnitLemma.Unr.IntBasis.exists_key
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:33:57.944118+00:00
-- url     : https://prove2.me/theorems/3485e507-8a43-433d-917b-b346cc0cea36
-- title:
--   Int Basis: exists key
-- statement:
--   The Int Basis construction uses the exists key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExt.lean#L49-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExt.lean#L49-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.IntBasis
open IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem GlobalTheory.UnitLemma.Unr.IntBasis.exists_key (h : IsUnrExt K K' d φ) :
    ∃ w : Fin d → K'.E, ∀ (a : Fin d → K.E) (m : Fin d), (∀ k, adicVal K (a k) ≤ adicVal K (a m)) →
      adicVal K' (∑ k, φ (a k) * w k) = adicVal K (a m) := by sorry
