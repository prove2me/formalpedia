-- Prove2me | Theorems.Thm_GlobalTheory_HermitianGauss_sum_pts_add
-- name    : GlobalTheory.HermitianGauss.sum_pts_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:39.005353+00:00
-- url     : https://prove2.me/theorems/7257e12a-340d-4277-aa8b-1b0222e7b1b8
-- title:
--   Hermitian Gauss: sum pts add
-- statement:
--   The Hermitian Gauss construction uses the sum pts add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L35-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]

theorem GlobalTheory.HermitianGauss.sum_pts_add (B : Submodule R M) (f : M → ℂ) {z : M} (hz : z ∈ B) :
    ∑ y ∈ pts B, f (y + z) = ∑ y ∈ pts B, f y := by sorry
