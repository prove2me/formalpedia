-- Prove2me | Theorems.Thm_GlobalTheory_BK_frob_mem_A
-- name    : GlobalTheory.BK.frob_mem_A
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:57.129994+00:00
-- url     : https://prove2.me/theorems/371ecb9e-dd7f-47ac-b430-687deacbeddf
-- title:
--   BK: frob mem A
-- statement:
--   The BK construction uses the frob mem A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L349-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L349-L354

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

theorem GlobalTheory.BK.frob_mem_A (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : f ∈ A O K) : frob K l f ∈ A O K := by sorry
