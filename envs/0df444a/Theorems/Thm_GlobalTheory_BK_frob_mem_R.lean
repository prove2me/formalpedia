-- Prove2me | Theorems.Thm_GlobalTheory_BK_frob_mem_R
-- name    : GlobalTheory.BK.frob_mem_R
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:43.967218+00:00
-- url     : https://prove2.me/theorems/60e97666-70a8-4318-b4fd-1c67cfad439a
-- title:
--   BK: frob mem R
-- statement:
--   The BK construction uses the frob mem R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L379-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L379-L384

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

theorem GlobalTheory.BK.frob_mem_R (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 ≤ k) {f : K⟦X⟧} (hf : f ∈ R O K l k) :
    frob K l f ∈ R O K l k := by sorry
