-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_exists_finset_span_image_eq
-- name    : GlobalTheory.ClassFin.exists_finset_span_image_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:41.888802+00:00
-- url     : https://prove2.me/theorems/0dc3c7d0-8554-4e22-9bde-9b9fa07e63ed
-- title:
--   Class Fin: exists finset span image eq
-- statement:
--   The Class Fin construction uses the exists finset span image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsCompletelyReducibleKroneckerOfSpanEqTop.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsCompletelyReducibleKroneckerOfSpanEqTop.lean#L12-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsometryMatrixRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsLogKronecker
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsConjHarmOfSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SsTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsCompletelyReducibleKroneckerOfSpanEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin

theorem GlobalTheory.ClassFin.exists_finset_span_image_eq {G V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : G → V) : ∃ T : Finset G, ∀ S : Set G, (T : Set G) ⊆ S →
      Submodule.span ℂ (f '' S) = Submodule.span ℂ (Set.range f) := by sorry
