-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_ss_range_toMatrix_iff_isSemisimpleRepresentation
-- name    : GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:11:21.840742+00:00
-- url     : https://prove2.me/theorems/f344dae5-1730-420c-b3c9-1082d3b9e930
-- title:
--   Class Fin: ss range to Matrix iff is Semisimple Representation
-- statement:
--   The Class Fin construction uses the ss range to Matrix iff is Semisimple Representation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CompletelyReducibleToMatrixIffIsSemisimpleRepres.lean#L21-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CompletelyReducibleToMatrixIffIsSemisimpleRepres.lean#L21-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CompletelyReducibleToMatrixIffIsSemisimpleRepres
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
open Matrix
open scoped Kronecker ComplexOrder TensorProduct

theorem GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V), _root_.GlobalTheory.ClassFin.SS (Set.range fun g => LinearMap.toMatrix b b (ρ g)) ↔ ρ.IsSemisimpleRepresentation := by sorry
