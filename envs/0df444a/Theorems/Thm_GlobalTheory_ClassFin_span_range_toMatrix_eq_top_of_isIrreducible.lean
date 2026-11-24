-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_span_range_toMatrix_eq_top_of_isIrreducible
-- name    : GlobalTheory.ClassFin.span_range_toMatrix_eq_top_of_isIrreducible
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:13:19.852522+00:00
-- url     : https://prove2.me/theorems/37fd3835-b5c3-46e3-8070-94f9242e89c1
-- title:
--   Class Fin: span range to Matrix eq top of is Irreducible
-- statement:
--   The Class Fin construction uses the span range to Matrix eq top of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodOfIsIrreducibleAl.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationTprodOfIsIrreducibleAl.lean#L11-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsCompletelyReducibleKroneckerOfSpanEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpanRangeEqTopOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CompletelyReducibleToMatrixIffIsSemisimpleRepres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodOfIsIrreducibleAl
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

theorem GlobalTheory.ClassFin.span_range_toMatrix_eq_top_of_isIrreducible {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (b : Module.Basis ι ℂ V) (h : ρ.IsIrreducible) :
    Submodule.span ℂ (Set.range
      ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ)) = ⊤ := by sorry
