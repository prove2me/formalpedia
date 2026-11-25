-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_coords_of_equiv
-- name    : GlobalTheory.SectionBasis.coords_of_equiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:53.3869+00:00
-- url     : https://prove2.me/theorems/274e2003-a015-5271-aa8f-a23e70e81978
-- title:
--   Section Basis: coords of equiv
-- statement:
--   The Section Basis construction uses the coords of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L385-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L385-L404

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct

theorem GlobalTheory.SectionBasis.coords_of_equiv {K' M ι : Type} [Field K'] [AddCommGroup M] [Module K' M] {Q : ι → Type}
    [∀ Z, CommRing (Q Z)] (a : ∀ Z, K' →+* Q Z) {n : ℕ} (b : Fin n → M) (hli : LinearIndependent K' b)
    (hsp : Submodule.span K' (Set.range b) = ⊤)
    (E : letI : ∀ Z, Module K' (Q Z) := fun Z => (a Z).toModule; M ≃ₗ[K'] ∀ Z, Q Z) :
    (∀ c : Fin n → K', (∀ Z, ∑ k, a Z (c k) * E (b k) Z = 0) → ∀ k, c k = 0) ∧
    ∀ y : ∀ Z, Q Z, ∃ c : Fin n → K', ∀ Z, y Z = ∑ k, a Z (c k) * E (b k) Z := by sorry
