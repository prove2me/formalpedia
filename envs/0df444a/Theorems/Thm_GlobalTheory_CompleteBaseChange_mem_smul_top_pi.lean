-- Prove2me | Theorems.Thm_GlobalTheory_CompleteBaseChange_mem_smul_top_pi
-- name    : GlobalTheory.CompleteBaseChange.mem_smul_top_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:05.563723+00:00
-- url     : https://prove2.me/theorems/5d128381-8633-499f-952a-280b45e6f08d
-- title:
--   Complete Base Change: mem smul top pi
-- statement:
--   The Complete Base Change construction uses the mem smul top pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L8-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L8-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange

theorem GlobalTheory.CompleteBaseChange.mem_smul_top_pi {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) (x : ι → M) :
    x ∈ (J • ⊤ : Submodule R (ι → M)) ↔ ∀ i, x i ∈ (J • ⊤ : Submodule R M) := by sorry
