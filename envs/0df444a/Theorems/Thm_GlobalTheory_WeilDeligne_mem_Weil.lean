-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_mem_Weil
-- name    : GlobalTheory.WeilDeligne.mem_Weil
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:09:54.453809+00:00
-- url     : https://prove2.me/theorems/0a1263c7-99e8-429c-a03e-02e7934e39bf
-- title:
--   Weil Deligne: mem Weil
-- statement:
--   The Weil Deligne construction uses the mem Weil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsNotCongPow.lean#L153-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsNotCongPow.lean#L153-L153

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable (h : IsPlaceOver A w)

theorem GlobalTheory.WeilDeligne.mem_Weil {σ : G E Ω} : σ ∈ Weil h ↔ ∃ a b, ActsAs A (normV w) σ a b := by sorry
