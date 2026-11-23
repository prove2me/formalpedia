-- Prove2me | Theorems.Thm_GlobalTheory_flag_basisMulGL_eq_iff
-- name    : GlobalTheory.flag_basisMulGL_eq_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:29.315443+00:00
-- url     : https://prove2.me/theorems/0033f631-ab68-4b1e-93f7-d20bac838d20
-- title:
--   Global Theory: flag basis Mul GL eq iff
-- statement:
--   The Global Theory construction uses the flag basis Mul GL eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L165-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L165-L180

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

theorem GlobalTheory.flag_basisMulGL_eq_iff (b : Basis (Fin n) R M) (g : GL (Fin n) R) :
    (basisMulGL b g).flag = b.flag ↔ g ∈ upperTriangularGL (Fin n) R := by sorry
