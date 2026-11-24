-- Prove2me | Theorems.Thm_GlobalTheory_flag_basisMulGL_le
-- name    : GlobalTheory.flag_basisMulGL_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:42.419525+00:00
-- url     : https://prove2.me/theorems/f8e4949f-202f-4e1f-a0f6-6bfe3176f937
-- title:
--   Global Theory: flag basis Mul GL le
-- statement:
--   The Global Theory construction uses the flag basis Mul GL le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L155-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L155-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]
variable {ι R}
variable {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}

theorem GlobalTheory.flag_basisMulGL_le (b : Basis (Fin n) R M) {g : GL (Fin n) R}
    (hg : g ∈ upperTriangularGL (Fin n) R) (k : Fin (n + 1)) :
    (basisMulGL b g).flag k ≤ b.flag k := by sorry
