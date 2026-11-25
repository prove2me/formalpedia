-- Prove2me | Theorems.Thm_GlobalTheory_CoefEmbed_norm_unit
-- name    : GlobalTheory.CoefEmbed.norm_unit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:52.59858+00:00
-- url     : https://prove2.me/theorems/d890ab79-e4b9-4655-82ec-703289bc9be7
-- title:
--   Coef Embed: norm unit
-- statement:
--   The Coef Embed construction uses the norm unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EmbeddingClosedIntegral.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EmbeddingClosedIntegral.lean#L41-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EmbeddingClosedIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoefEmbed
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem GlobalTheory.CoefEmbed.norm_unit (f : O →+* PadicAlgCl l)
    (hf : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))
    {a : O} (ha : IsUnit a) : ‖f a‖ = 1 := by sorry
