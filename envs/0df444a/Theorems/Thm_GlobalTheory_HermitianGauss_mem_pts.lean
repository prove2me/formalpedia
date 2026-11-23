-- Prove2me | Theorems.Thm_GlobalTheory_HermitianGauss_mem_pts
-- name    : GlobalTheory.HermitianGauss.mem_pts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:35.734798+00:00
-- url     : https://prove2.me/theorems/56cdba93-7d56-481f-a3a2-801f2c00d240
-- title:
--   Hermitian Gauss: mem pts
-- statement:
--   The Hermitian Gauss construction uses the mem pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L16-L16

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

theorem GlobalTheory.HermitianGauss.mem_pts {B : Submodule R M} {x : M} : x ∈ pts B ↔ x ∈ B := by sorry
