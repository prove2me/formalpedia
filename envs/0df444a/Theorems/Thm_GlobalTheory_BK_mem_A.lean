-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_A
-- name    : GlobalTheory.BK.mem_A
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:48.945313+00:00
-- url     : https://prove2.me/theorems/0b8947f7-cf27-52b8-a629-06e683d6b624
-- title:
--   BK: mem A
-- statement:
--   The BK construction uses the mem A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L110-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L110-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}

theorem GlobalTheory.BK.mem_A {f : K⟦X⟧} : f ∈ A O K ↔ ∀ n, ‖coeff n f‖ ≤ 1 := by sorry
