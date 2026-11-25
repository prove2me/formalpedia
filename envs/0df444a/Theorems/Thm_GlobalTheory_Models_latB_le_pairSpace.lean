-- Prove2me | Theorems.Thm_GlobalTheory_Models_latB_le_pairSpace
-- name    : GlobalTheory.Models.latB_le_pairSpace
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:12.813128+00:00
-- url     : https://prove2.me/theorems/a43b78d3-63f6-5ea3-abc9-de9297622592
-- title:
--   Models: lat B le pair Space
-- statement:
--   The Models construction uses the lat B le pair Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L246-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L246-L263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
variable {l n : ℕ} {R : RingPG k l}

theorem GlobalTheory.Models.latB_le_pairSpace {m r : ℕ} {D : ModPG R n (Vc k m)} {Dt : TopData n r} {N : Lats k n m}
    (h : ABC D Dt.w Dt.wst N) : latB D N ≤ pairSpace D Dt N := by sorry
