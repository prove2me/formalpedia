-- Prove2me | Theorems.Thm_GlobalTheory_flag_eq_flag_iff
-- name    : GlobalTheory.flag_eq_flag_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:38.439053+00:00
-- url     : https://prove2.me/theorems/7e2c5354-40d1-4773-908d-ee7ca8a96db1
-- title:
--   Global Theory: flag eq flag iff
-- statement:
--   The Global Theory construction uses the flag eq flag iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L182-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L182-L184

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

theorem GlobalTheory.flag_eq_flag_iff (b b' : Basis (Fin n) R M) :
    b'.flag = b.flag ↔ basisChange b b' ∈ upperTriangularGL (Fin n) R := by sorry
