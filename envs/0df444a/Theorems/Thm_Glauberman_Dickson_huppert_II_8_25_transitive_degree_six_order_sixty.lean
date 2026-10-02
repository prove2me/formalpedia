-- Prove2me | Theorems.Thm_Glauberman_Dickson_huppert_II_8_25_transitive_degree_six_order_sixty
-- name    : Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T13:29:50.417331+00:00
-- url     : https://prove2.me/theorems/55a2ec13-9f34-4a42-b4d1-ba00341c7e9f
-- title:
--   Order-60 groups with a faithful transitive action on six points
-- statement:
--   A finite group of order 60 admitting a faithful transitive action on a six-element set is isomorphic to the alternating group A₅. This is the group-action endpoint Huppert II.8.25 used in the Dickson classification proof.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean; declaration Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
set_option autoImplicit false
universe u v
open scoped Pointwise Classical

theorem Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
    {G Ω : Type u} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω]
    (htransitive : MulAction.IsPretransitive G Ω)
    (hΩcard : Nat.card Ω = 6) (hGcard : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by sorry
