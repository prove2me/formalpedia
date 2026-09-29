-- Prove2me | Theorems.Thm_Matrix_exists_eq_smul_one_of_commute_of_map_span_eq_top
-- name    : Matrix.exists_eq_smul_one_of_commute_of_map_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/94278303-6e93-5df3-ba65-06aeedcc57dd
-- title:
--   Commutant of a residually spanning set of matrices is scalar
-- statement:
--   Let $n$ be a finite index type with decidable equality, let $A$ be a commutative local ring, let $k$ be a field, and let $\pi : A \to k$ be a surjective ring homomorphism. Let $S$ be a set of $n \times n$ matrices over $A$ and suppose that the image of $S$ under entrywise application of $\pi$, i.e. the set of matrices $X.\mathrm{map}\,\pi$ for $X \in S$, spans the whole $k$-module $M_n(k)$. Let $M \in M_n(A)$ be a matrix such that $X M = M X$ for every $X \in S$. The conclusion is that there exists $a \in A$ with $M = a \cdot 1$, that is, $M$ is the scalar matrix $a I_n$ (written as the scalar multiple $a \bullet 1$ of the identity matrix). Note that $\pi$ is an arbitrary surjection onto a field, not assumed to be the residue map of $A$; no irreducibility or group-theoretic structure on $S$ is involved, only the spanning condition on its reduction.
--
--   This is the form of Schur's lemma used in deformation theory: for a lift $\rho$ of a residually absolutely irreducible representation, Burnside's theorem makes the reductions of the matrices $\rho(g)$ span $M_n(k)$, so any endomorphism of $\rho$ is a scalar. It is cited by [`Deformation.exists_eq_smul_one_of_commute`](thm.html#Deformation.exists_eq_smul_one_of_commute), which supplies this statement in the setting of lifts of a residual representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_eq_smul_one_of_commute_of_map_span_eq_top.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.exists_eq_smul_one_of_commute_of_map_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] [IsLocalRing A]
    {k : Type*} [Field k] (π : A →+* k) (hπ : Function.Surjective π)
    {S : Set (Matrix n n A)}
    (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤)
    (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) : ∃ a : A, M = a • 1 := by sorry
