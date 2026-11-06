-- Prove2me | Theorems.Thm_OAI_ShortDraftLatticeCount_finite_lattice_count
-- name    : OAI.ShortDraftLatticeCount.finite_lattice_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:19:02.313952+00:00
-- url     : https://prove2.me/theorems/ffb3d235-4d25-442c-b070-f766cec7bac0
-- title:
--   Short Draft Lattice Count: finite lattice count
-- statement:
--   The Short Draft Lattice Count construction uses the finite lattice count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L27-L54
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L27-L54

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

theorem OAI.ShortDraftLatticeCount.finite_lattice_count (S : Finset (ℤ × ℤ)) (D R : ℕ)
    (hR : 2 * D < R ^ 2)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ (2 * R + 1) ^ 2 := by sorry
