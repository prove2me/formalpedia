-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_qPow_add
-- name    : GlobalTheory.WeilDeligne.qPow_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:09:57.939022+00:00
-- url     : https://prove2.me/theorems/8bbc3a90-e813-42b9-9e75-54247474a8c0
-- title:
--   Weil Deligne: q Pow add
-- statement:
--   The Weil Deligne construction uses the q Pow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsNotCongPow.lean#L270-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsNotCongPow.lean#L270-L272

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

theorem GlobalTheory.WeilDeligne.qPow_add (s t : ℝ) : qPow w (s + t) = qPow w s * qPow w t := by sorry
