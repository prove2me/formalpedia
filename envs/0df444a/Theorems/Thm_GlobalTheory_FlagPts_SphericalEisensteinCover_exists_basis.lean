-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_exists_basis
-- name    : GlobalTheory.FlagPts.SphericalEisensteinCover.exists_basis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:55.829551+00:00
-- url     : https://prove2.me/theorems/08696301-e18b-5249-b750-03d2ae92d2a1
-- title:
--   Spherical Eisenstein Cover: exists basis
-- statement:
--   The Spherical Eisenstein Cover construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L121-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L121-L219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

theorem GlobalTheory.FlagPts.SphericalEisensteinCover.exists_basis (Fs : ℕ → Submodule k W) (hmono : ∀ m, Fs m ≤ Fs (m + 1))
    (hdim : ∀ m, finrank k (Fs m) = min m (finrank k W)) (A B : Submodule k W) (hN : 2 ≤ finrank k W)
    (hAB : A ≤ B) (hA : finrank k A = 1) (hB : finrank k B + 1 = finrank k W) :
    ∃ b : Basis (Fin (finrank k W)) k W, (∀ a : Fin (finrank k W), (a : ℕ) = 0 → b a ∈ A) ∧
      (∀ a : Fin (finrank k W), (a : ℕ) + 1 < finrank k W → b a ∈ B) ∧
      ∀ m, Disjoint (Fs m) (Submodule.span k (b '' {a : Fin (finrank k W) | m ≤ (a : ℕ)})) := by sorry
