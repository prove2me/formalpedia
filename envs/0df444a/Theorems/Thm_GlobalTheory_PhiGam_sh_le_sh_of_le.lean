-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_sh_le_sh_of_le
-- name    : GlobalTheory.PhiGam.sh_le_sh_of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:15.069473+00:00
-- url     : https://prove2.me/theorems/27066d90-7579-4a4c-a3c4-bf8374b49d08
-- title:
--   Phi Gam: sh le sh of le
-- statement:
--   The Phi Gam construction uses the sh le sh of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L133-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L133-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
variable [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem GlobalTheory.PhiGam.sh_le_sh_of_le {a b : ℤ} (h : b ≤ a) (N : Submodule k⟦X⟧ V) : sh a N ≤ sh b N := by sorry
