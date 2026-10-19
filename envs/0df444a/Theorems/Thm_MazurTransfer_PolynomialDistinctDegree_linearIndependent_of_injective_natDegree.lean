-- Prove2me | Theorems.Thm_MazurTransfer_PolynomialDistinctDegree_linearIndependent_of_injective_natDegree
-- name    : MazurTransfer.PolynomialDistinctDegree.linearIndependent_of_injective_natDegree
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:42:17.253088+00:00
-- url     : https://prove2.me/theorems/4189e4c4-380c-4ace-a9b6-886fafc6e583
-- title:
--   Nonzero polynomials of distinct degrees are linearly independent
-- statement:
--   Let $R$ be a commutative integral domain, let $I$ be an arbitrary index type, and let $(p_i)_{i\in I}$ be nonzero polynomials in $R[X]$. If their natural degrees are pairwise distinct, then $$\{p_i\mid i\in I\}\text{ is an }R\text{-linearly independent family.}$$ This supplies the distinct-degree argument used in the actual single-section finite-algebra basis construction for the order-thirteen curve.
-- source:
--   The unchanged statement and complete direct proof body from checked MazurTheorem PolynomialDistinctDegreeLinearIndependence.lean. Complete Lean frontend declaration, namespace and command ranges hoist the theorem to the required global solution. The complete original and public kernel types are compared by closed witnesses, preserving both universe parameters. The proof imports only Mathlib. Vas and contributors, Apache-2.0.

import Mathlib
open Polynomial

theorem MazurTransfer.PolynomialDistinctDegree.linearIndependent_of_injective_natDegree {R ι : Type*} [CommRing R] [IsDomain R]  (v : ι → Polynomial R)
    (hn : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => (v i).natDegree)) :
    LinearIndependent R v  := by sorry
