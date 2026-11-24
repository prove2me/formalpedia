-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_sh_sh_eq
-- name    : GlobalTheory.PhiGam.sh_sh_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:44:37.99104+00:00
-- url     : https://prove2.me/theorems/8cabd8ce-e722-46a8-bf42-6c6dbfbebe09
-- title:
--   Phi Gam: sh sh eq
-- statement:
--   The Phi Gam construction uses the sh sh eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L126-L128

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

theorem GlobalTheory.PhiGam.sh_sh_eq (a b : ℤ) (N : Submodule k⟦X⟧ V) : sh a (sh b N) = sh (a + b) N := by sorry
