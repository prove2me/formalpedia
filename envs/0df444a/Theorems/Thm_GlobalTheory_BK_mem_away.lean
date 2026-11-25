-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_away
-- name    : GlobalTheory.BK.mem_away
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:08.003798+00:00
-- url     : https://prove2.me/theorems/946086b7-04d9-4f8b-b1c4-12877d098d82
-- title:
--   BK: mem away
-- statement:
--   The BK construction uses the mem away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L198-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L198-L199

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

theorem GlobalTheory.BK.mem_away {B : Subalgebra O K⟦X⟧} {s : B} {f : K⟦X⟧} :
    f ∈ away B s ↔ ∃ n : ℕ, (s : K⟦X⟧) ^ n * f ∈ B := by sorry
