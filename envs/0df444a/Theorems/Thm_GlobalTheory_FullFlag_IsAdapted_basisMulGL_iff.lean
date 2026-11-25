-- Prove2me | Theorems.Thm_GlobalTheory_FullFlag_IsAdapted_basisMulGL_iff
-- name    : GlobalTheory.FullFlag.IsAdapted.basisMulGL_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:56.004824+00:00
-- url     : https://prove2.me/theorems/0735fa79-a0ac-4e02-9a40-329fa695ce30
-- title:
--   Is Adapted: basis Mul GL iff
-- statement:
--   The Is Adapted construction uses the basis Mul GL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L261-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L261-L263

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}

theorem GlobalTheory.FullFlag.IsAdapted.basisMulGL_iff {F : FullFlag R M n} {b : Basis (Fin n) R M} (hb : F.IsAdapted b)
    (g : GL (Fin n) R) : F.IsAdapted (basisMulGL b g) ↔ g ∈ upperTriangularGL (Fin n) R := by sorry
