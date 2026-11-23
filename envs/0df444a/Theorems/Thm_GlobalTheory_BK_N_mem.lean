-- Prove2me | Theorems.Thm_GlobalTheory_BK_N_mem
-- name    : GlobalTheory.BK.N_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:47.096887+00:00
-- url     : https://prove2.me/theorems/b6d619c6-8db9-4229-b0b6-7197c6687b2a
-- title:
--   BK: N mem
-- statement:
--   The BK construction uses the N mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L453-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L453-L454

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
omit [IsUltrametricDist K] [IsUnitBall O K]

theorem GlobalTheory.BK.N_mem {B : Subalgebra O K⟦X⟧} [HasU B] {f : K⟦X⟧} (hf : PowerSeries.derivative K f ∈ B) :
    N K f ∈ B := by sorry
