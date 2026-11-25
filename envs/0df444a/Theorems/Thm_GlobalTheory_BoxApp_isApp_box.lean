-- Prove2me | Theorems.Thm_GlobalTheory_BoxApp_isApp_box
-- name    : GlobalTheory.BoxApp.isApp_box
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:12.455973+00:00
-- url     : https://prove2.me/theorems/c0d63ad5-0a02-4fa7-9d09-261a7077f0d1
-- title:
--   Box App: is App box
-- statement:
--   The Box App construction uses the is App box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/IsAppBox.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/IsAppBox.lean#L16-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_IsAppBox
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory GlobalTheory.BoxApp

theorem GlobalTheory.BoxApp.isApp_box {R : Type} [CommRing R] [IsDomain R] {D D₂ D' : DegPre R} {n₁ n₂ : ℕ} (pD₂ : IsPowDeg D₂ D n₂)
    (pD : IsPowDeg D' D (n₁ + n₂)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (a : Fin n₁ → Fam D F k) (u : Fin n₂ → Fam D F k) (sb : Fam D₂ F k) (S : Fam D' F k)
    (h₂ : IsBoxFam pD₂ F k sb u) (h : IsBoxFam pD F k S (Fin.append a u)) : IsApp pD₂ pD F k a sb S := by sorry
