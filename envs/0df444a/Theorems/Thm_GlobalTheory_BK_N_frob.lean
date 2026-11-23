-- Prove2me | Theorems.Thm_GlobalTheory_BK_N_frob
-- name    : GlobalTheory.BK.N_frob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:00.417945+00:00
-- url     : https://prove2.me/theorems/d628bd2c-1acc-4efe-89ea-792a3d676ba6
-- title:
--   BK: N frob
-- statement:
--   The BK construction uses the N frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L297-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L297-L305

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

theorem GlobalTheory.BK.N_frob (l : ℕ) [Fact l.Prime] (f : K⟦X⟧) :
    N K (frob K l f) = (l : K⟦X⟧) * frob K l (N K f) := by sorry
