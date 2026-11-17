-- Prove2me | Theorems.Thm_MvPolynomial_exists_homogeneous_bezout_mod_ideal
-- name    : MvPolynomial.exists_homogeneous_bezout_mod_ideal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:53.077287+00:00
-- url     : https://prove2.me/theorems/fb23d796-e0d7-4488-bf6c-7f6d119ae40a
-- title:
--   A homogeneous zero-locus condition gives projective Bézout identities modulo the ideal
-- statement:
--   Let $K$ be a field, let $I⊆K[X_s:s∈S]$ be homogeneous, and let $ι:T→S$ with $S,T$ finite. Assume that over $\overline K$ the common zero locus of $I$ together with the coordinates $X_{ι(t)}$ consists only of the origin. Then there exist $D∈ℕ$ and homogeneous polynomials $q_{s,t}$ of degree $D$ such that, for every $s∈S$, $$X_s^{D+1}-∑_{t∈T}q_{s,t}X_{ι(t)}∈I.$$ This is the homogeneous Bézout certificate used to compare projective heights.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial

theorem MvPolynomial.exists_homogeneous_bezout_mod_ideal
    {K : Type} [Field K] {S T : Type} [Fintype S] [Fintype T]
    (I : Ideal (MvPolynomial S K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule S K))
    (inc : T → S)
    (hzero : ∀ z : S → AlgebraicClosure K,
      z ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
        (I ⊔ Ideal.span (Set.range
          (fun i : T => (MvPolynomial.X (inc i) : MvPolynomial S K)))) → z = 0) :
    ∃ (D : ℕ) (q : S × T → MvPolynomial S K),
      (∀ a, (q a).IsHomogeneous D) ∧
      ∀ k : S,
        MvPolynomial.X k ^ (D + 1) -
          ∑ i : T, q (k, i) * MvPolynomial.X (inc i) ∈ I := by sorry
