-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_crtAut_apply
-- name    : GlobalTheory.LevDesc.crtAut_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:34.445444+00:00
-- url     : https://prove2.me/theorems/0a46781b-83d8-4901-bfd6-5c747caad8f9
-- title:
--   Lev Desc: crt Aut apply
-- statement:
--   The Lev Desc construction uses the crt Aut apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L329-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L329-L329

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {O : Type} [CommRing O] (N : Type) [AddCommGroup N] [Module O N]
variable {N} {I J : Ideal O}
variable {ι : Type} [Finite ι] {Js : ι → Ideal O} (hle : ∀ i, I ≤ Js i)
  (hc : Pairwise (Function.onFun IsCoprime Js)) (hI : ⨅ i, Js i ≤ I)

theorem GlobalTheory.LevDesc.crtAut_apply (γ : QAut N I) (i : ι) : crtAut hle hc hI γ i = autRed (hle i) γ := by sorry
