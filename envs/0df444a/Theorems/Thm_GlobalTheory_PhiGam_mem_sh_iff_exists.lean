-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_mem_sh_iff_exists
-- name    : GlobalTheory.PhiGam.mem_sh_iff_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:13.564921+00:00
-- url     : https://prove2.me/theorems/b9510437-f633-40e8-864c-cbfad805c566
-- title:
--   Phi Gam: mem sh iff exists
-- statement:
--   The Phi Gam construction uses the mem sh iff exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L109-L110

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

theorem GlobalTheory.PhiGam.mem_sh_iff_exists {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ ∃ y ∈ N, vv k ^ a • y = x := by sorry
