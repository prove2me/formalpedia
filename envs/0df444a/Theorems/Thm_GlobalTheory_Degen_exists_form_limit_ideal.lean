-- Prove2me | Theorems.Thm_GlobalTheory_Degen_exists_form_limit_ideal
-- name    : GlobalTheory.Degen.exists_form_limit_ideal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:14.531856+00:00
-- url     : https://prove2.me/theorems/a1262e8b-ee29-4df1-a182-069c95386cf1
-- title:
--   Degen: exists form limit ideal
-- statement:
--   The Degen construction uses the exists form limit ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormLimitIdeal.lean#L7-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormLimitIdeal.lean#L7-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFormLimitIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Degen
open MvPolynomial

theorem GlobalTheory.Degen.exists_form_limit_ideal (R : Type) [CommRing R] (I : Ideal R) (hI : IsAdicComplete I R)
    (σ : Type) [Finite σ] (K : ℕ → Ideal (MvPolynomial σ R)) (t : ℕ)
    (hK : ∀ e F, F.IsHomogeneous t → F ∈ K (e + 1) → F ∈ K e)
    (ha : ∀ e, ∀ a ∈ I ^ (e + 1), MvPolynomial.C a ∈ K e)
    (hs : ∀ e F, F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial σ R, G.IsHomogeneous t ∧
      (∀ d, MvPolynomial.coeff d G ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1))
    (e : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous t) (hFe : F ∈ K e) :
    ∃ F₁ : MvPolynomial σ R, F₁.IsHomogeneous t ∧ (∀ e', F₁ ∈ K e') ∧
      ∀ d, MvPolynomial.coeff d (F - F₁) ∈ I ^ (e + 1) := by sorry
