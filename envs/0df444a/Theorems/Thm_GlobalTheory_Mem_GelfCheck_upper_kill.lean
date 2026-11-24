-- Prove2me | Theorems.Thm_GlobalTheory_Mem_GelfCheck_upper_kill
-- name    : GlobalTheory.Mem.GelfCheck.upper_kill
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:59.874886+00:00
-- url     : https://prove2.me/theorems/c4fc065a-621e-410a-b3b7-4d1f91c803d9
-- title:
--   Gelf Check: upper kill
-- statement:
--   The Gelf Check construction uses the upper kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L164-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L164-L176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V}

theorem GlobalTheory.Mem.GelfCheck.upper_kill (h : GlRel E) (hv : ∀ a b, a < b → E a b v = 0) (k : ℕ) (a b : Fin N) (hab : a < b) :
    (E ^ k) a b v = 0 := by sorry
