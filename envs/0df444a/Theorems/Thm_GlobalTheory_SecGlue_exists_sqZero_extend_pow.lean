-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_exists_sqZero_extend_pow
-- name    : GlobalTheory.SecGlue.exists_sqZero_extend_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:49:12.624018+00:00
-- url     : https://prove2.me/theorems/360392bf-31df-49de-999d-b09cecffd08a
-- title:
--   Sec Glue: exists sq Zero extend pow
-- statement:
--   The Sec Glue construction uses the exists sq Zero extend pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSqZeroExtendLocalizationAwayPow.lean#L137-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSqZeroExtendLocalizationAwayPow.lean#L137-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue

theorem GlobalTheory.SecGlue.exists_sqZero_extend_pow : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by sorry
