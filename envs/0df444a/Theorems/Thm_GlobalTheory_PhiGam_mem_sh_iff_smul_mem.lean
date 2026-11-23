-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_mem_sh_iff_smul_mem
-- name    : GlobalTheory.PhiGam.mem_sh_iff_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:35.312798+00:00
-- url     : https://prove2.me/theorems/d58ab2fa-16ac-4727-b110-7baff6f9f0af
-- title:
--   Phi Gam: mem sh iff smul mem
-- statement:
--   The Phi Gam construction uses the mem sh iff smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L112-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L112-L121

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

theorem GlobalTheory.PhiGam.mem_sh_iff_smul_mem {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ vv k ^ (-a) • x ∈ N := by sorry
