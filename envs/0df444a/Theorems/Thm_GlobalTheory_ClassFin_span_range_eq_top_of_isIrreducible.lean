-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_span_range_eq_top_of_isIrreducible
-- name    : GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:18.076346+00:00
-- url     : https://prove2.me/theorems/7d30b171-e4b3-4697-93c2-ae79058315b1
-- title:
--   Class Fin: span range eq top of is Irreducible
-- statement:
--   The Class Fin construction uses the span range eq top of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SpanRangeEqTopOfIsIrreducible.lean#L62-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SpanRangeEqTopOfIsIrreducible.lean#L62-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpanRangeEqTopOfIsIrreducible
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
open scoped MonoidAlgebra
open Matrix
open scoped Kronecker ComplexOrder TensorProduct
open scoped MonoidAlgebra

theorem GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) [FiniteDimensional ℂ V], ρ.IsIrreducible → Submodule.span ℂ (Set.range ρ) = ⊤ := by sorry
