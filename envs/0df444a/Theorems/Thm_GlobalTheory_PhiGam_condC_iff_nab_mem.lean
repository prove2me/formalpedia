-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_condC_iff_nab_mem
-- name    : GlobalTheory.PhiGam.condC_iff_nab_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:29.960916+00:00
-- url     : https://prove2.me/theorems/7618b59f-6c13-4aa1-ad26-34740796a2fe
-- title:
--   Phi Gam: cond C iff nab mem
-- statement:
--   The Phi Gam construction uses the cond C iff nab mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L162-L164

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

theorem GlobalTheory.PhiGam.condC_iff_nab_mem [Module k V] [IsScalarTower k k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
    (g : V →ₗ[k] V) (N : Submodule k⟦X⟧ V) : CondC g N ↔ ∀ x ∈ N, nab g x ∈ N := by sorry
