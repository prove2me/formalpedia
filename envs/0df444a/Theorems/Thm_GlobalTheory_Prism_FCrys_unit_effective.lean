-- Prove2me | Theorems.Thm_GlobalTheory_Prism_FCrys_unit_effective
-- name    : GlobalTheory.Prism.FCrys.unit_effective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:15.260938+00:00
-- url     : https://prove2.me/theorems/53dcd04a-8e22-4d4c-a991-286dd2a3705b
-- title:
--   FCrys: unit effective
-- statement:
--   The FCrys construction uses the unit effective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L311-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L311-L316

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InvertibleSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Prism
attribute [instance] Obj.ring
variable {l : ℕ} {R : Type} [CommRing R]
attribute [instance] FCrys.acg FCrys.mod
attribute [instance] VBun.acg VBun.mod

theorem GlobalTheory.Prism.FCrys.unit_effective (l : ℕ) (R : Type) [CommRing R] : (FCrys.unit l R).Effective := by sorry
