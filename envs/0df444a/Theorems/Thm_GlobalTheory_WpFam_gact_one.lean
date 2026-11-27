-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_gact_one
-- name    : GlobalTheory.WpFam.gact_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:53.62209+00:00
-- url     : https://prove2.me/theorems/14ddc8f9-d3ba-5581-ba07-76c5838ec7e3
-- title:
--   Wp Fam: gact one
-- statement:
--   The Wp Fam construction uses the gact one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ZetaActRefl.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ZetaActRefl.lean#L79-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups Matrix
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.WpFam

theorem GlobalTheory.WpFam.gact_one (N : ℕ) (α : GL (Fin 2) (ZMod N)) (γ : SL(2, ℤ)) : gact N 1 α γ = α * redGL N γ := by sorry
