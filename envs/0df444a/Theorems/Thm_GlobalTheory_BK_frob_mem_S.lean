-- Prove2me | Theorems.Thm_GlobalTheory_BK_frob_mem_S
-- name    : GlobalTheory.BK.frob_mem_S
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:59.820272+00:00
-- url     : https://prove2.me/theorems/e2dcdebd-1a20-4e1e-a865-b7be4beca910
-- title:
--   BK: frob mem S
-- statement:
--   The BK construction uses the frob mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L363-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L363-L368

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

theorem GlobalTheory.BK.frob_mem_S (l : ℕ) [Fact l.Prime] {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) :
    frob K l f ∈ S O K e := by sorry
