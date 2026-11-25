-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
-- name    : GlobalTheory.WeilDeligne.coe_qPow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:07:58.455271+00:00
-- url     : https://prove2.me/theorems/d352a6e5-5956-411b-ad18-0b603257f9e4
-- title:
--   Weil Deligne: coe q Pow
-- statement:
--   The Weil Deligne construction uses the coe q Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsNotCongPow.lean#L262-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsNotCongPow.lean#L262-L262

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
variable {h}
variable [IsAlgClosure E Ω]
omit [IsAlgClosure E Ω]

theorem GlobalTheory.WeilDeligne.coe_qPow (s : ℝ) : (qPow w s : ℂ) = ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) := by sorry

attribute [defeq] GlobalTheory.WeilDeligne.coe_qPow
