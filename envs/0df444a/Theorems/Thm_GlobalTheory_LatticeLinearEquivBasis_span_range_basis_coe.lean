-- Prove2me | Theorems.Thm_GlobalTheory_LatticeLinearEquivBasis_span_range_basis_coe
-- name    : GlobalTheory.LatticeLinearEquivBasis.span_range_basis_coe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:00:22.191454+00:00
-- url     : https://prove2.me/theorems/baca9d93-b955-41b3-8a88-6f5f7395ba65
-- title:
--   Lattice Linear Equiv Basis: span range basis coe
-- statement:
--   The Lattice Linear Equiv Basis construction uses the span range basis coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsLinearEquivMapLatticeEq.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsLinearEquivMapLatticeEq.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsLinearEquivMapLatticeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.LatticeLinearEquivBasis
open Module

theorem GlobalTheory.LatticeLinearEquivBasis.span_range_basis_coe {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    {ι : Type*} (A : Submodule R V) (b : Basis ι R A) :
    Submodule.span R (Set.range fun i => (b i : V)) = A := by sorry
