-- Prove2me | Theorems.Thm_OAI_ShortDraftLatticeCount_finite_multiples_count
-- name    : OAI.ShortDraftLatticeCount.finite_multiples_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:19:12.999428+00:00
-- url     : https://prove2.me/theorems/633acdd6-3b4a-42a9-8bc6-c662f1a36e43
-- title:
--   Short Draft Lattice Count: finite multiples count
-- statement:
--   The Short Draft Lattice Count construction uses the finite multiples count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L238-L254
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L238-L254

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ShortDraftLatticeCount
open ActualEisensteinCoordinates

theorem OAI.ShortDraftLatticeCount.finite_multiples_count
    (p : O) (hp : p ≠ 0) (T : Finset O) (D : ℕ)
    (hT : ∀ x ∈ T, qNat (p * x) ≤ D) :
    T.card ≤ 64 * (D / qNat p + 1) := by sorry
