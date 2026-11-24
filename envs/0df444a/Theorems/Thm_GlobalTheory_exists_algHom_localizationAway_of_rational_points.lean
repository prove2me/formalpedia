-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_localizationAway_of_rational_points
-- name    : GlobalTheory.exists_algHom_localizationAway_of_rational_points
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:12.491497+00:00
-- url     : https://prove2.me/theorems/a52dde2a-bfef-4138-9946-570cace5888b
-- title:
--   Global Theory: exists alg Hom localization Away of rational points
-- statement:
--   The Global Theory construction uses the exists alg Hom localization Away of rational points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAlgHomLocalizationAwayOfRationalPoints.lean#L30-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAlgHomLocalizationAwayOfRationalPoints.lean#L30-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAlgHomLocalizationAwayOfRationalPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial

theorem GlobalTheory.exists_algHom_localizationAway_of_rational_points :
    ∀ (k : Type) [Field k] [Infinite k] (A : Type) [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → Pd ≠ 0 → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → ∃ χ : A →ₐ[k] Localization.Away (Polynomial.X * Pd), ∀ i, χ (f i) * algebraMap (Polynomial k) _ Pd = algebraMap (Polynomial k) _ (P i) := by sorry
