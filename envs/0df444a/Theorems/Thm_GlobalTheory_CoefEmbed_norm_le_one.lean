-- Prove2me | Theorems.Thm_GlobalTheory_CoefEmbed_norm_le_one
-- name    : GlobalTheory.CoefEmbed.norm_le_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:41.699606+00:00
-- url     : https://prove2.me/theorems/b81cee50-0034-4b42-81c4-b4b24c540637
-- title:
--   Coef Embed: norm le one
-- statement:
--   The Coef Embed construction uses the norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EmbeddingClosedIntegral.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EmbeddingClosedIntegral.lean#L9-L39

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

theorem GlobalTheory.CoefEmbed.norm_le_one (f : O →+* PadicAlgCl l)
    (hf : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))
    (a : O) : ‖f a‖ ≤ 1 := by sorry
