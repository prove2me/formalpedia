-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_gsum_lowerOrder_inl
-- name    : GlobalTheory.PMonE.gsum_lowerOrder_inl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:39:45.426064+00:00
-- url     : https://prove2.me/theorems/93d654b6-df05-4d00-8338-0fc69b0eb8f4
-- title:
--   PMon E: gsum lower Order inl
-- statement:
--   The PMon E construction uses the gsum lower Order inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSurjectivityOfOne.lean#L54-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSurjectivityOfOne.lean#L54-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

theorem GlobalTheory.PMonE.gsum_lowerOrder_inl (q : ℕ) {K D : ℕ} (hD : K + 1 ≤ D) (M : ℕ → Matrix m m F) (z : m ⊕ m → F) (i : m) :
    gsum q D (lowerOrder (K + 1) M) z (Sum.inl i) = z (Sum.inl i) ^ q ^ (K + 1) - z (Sum.inr i) ^ q ^ K := by sorry
