-- Prove2me | Theorems.Thm_Matrix_exists_eq_smul_one_of_commute_of_span_eq_top
-- name    : Matrix.exists_eq_smul_one_of_commute_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/0664ca93-4ac7-5f9e-b6d3-d18ad7301cc3
-- title:
--   Matrices commuting with a spanning set are scalar
-- statement:
--   Let $n$ be a finite index type with decidable equality, let $A$ be a commutative ring, and let $S$ be a set of $n \times n$ matrices over $A$ whose $A$-submodule span inside $\mathrm{Matrix}\,n\,n\,A$ is the whole module, i.e. $\mathrm{span}_A(S) = \top$. Let $M$ be an $n \times n$ matrix over $A$ such that $X M = M X$ for every $X \in S$. Then there exists a scalar $a \in A$ with $M = a \cdot 1$, where $1$ is the identity matrix and the product is the scalar action of $A$ on matrices. Thus commuting with the members of an $A$-spanning set of the full matrix algebra already forces $M$ to be a scalar matrix; no irreducibility or finiteness hypothesis on $A$ is needed, and the scalar $a$ is produced by an existential statement rather than as an explicit function of $M$.
--
--   This is the matrix form of Schur's lemma over a commutative ring: the commutant of an $A$-spanning subset of $M_n(A)$ is the centre of $M_n(A)$, which consists of the scalar matrices. It is used in the characterisation of absolute irreducibility of a representation, [`Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end`](thm.html#Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end), and thereby in the Schur-type input to the deformation-theoretic part of the argument, where the centralizer of a lift of an absolutely irreducible residual representation must be scalar.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_eq_smul_one_of_commute_of_span_eq_top.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.exists_eq_smul_one_of_commute_of_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A]
    {S : Set (Matrix n n A)} (hS : Submodule.span A S = ⊤)
    (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) :
    ∃ a : A, M = a • 1 := by sorry
