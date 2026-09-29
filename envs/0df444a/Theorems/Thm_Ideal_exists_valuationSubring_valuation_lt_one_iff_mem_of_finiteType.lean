-- Prove2me | Theorems.Thm_Ideal_exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType
-- name    : Ideal.exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/343ce291-ef9c-5b6c-9b78-0741a22d4f2f
-- title:
--   Non-zero primes of affine domains are centres of prime divisors
-- statement:
--   Let $k$ be a field, let $A$ be a commutative integral domain which is a $k$-algebra of finite type, and let $K$ be a field equipped with an $A$-algebra structure making it a fraction field of $A$, together with a $k$-algebra structure compatible with that of $A$ (a scalar tower $k \to A \to K$). Let $p \subseteq A$ be a prime ideal with $p \neq \bot$. The assertion is that there exist a valuation subring $O$ of $K$, a natural number $d$ and a family $f : \mathrm{Fin}\, d \to K$ such that: $O \neq \top$, i.e. $O$ is a proper subring of $K$; the image of every $a \in A$ under $A \to K$ lies in $O$; for every $a \in A$ the valuation attached to $O$ satisfies $\mathrm{val}(a) < 1$ exactly when $a \in p$, so that the centre of $O$ on $A$ is $p$; the image of $d + 1$ in $\mathrm{WithBot}\, \mathbb{N}\infty$ equals $\mathrm{ringKrullDim}\, A$; each $f\, i$ lies in $O$; and every polynomial $Q \in k[X_i : i \in \mathrm{Fin}\, d]$ with $\mathrm{val}(Q(f)) < 1$, where $Q(f)$ denotes the evaluation of $Q$ at the family $f$ over $k$, is the zero polynomial. The last condition says that the residues of $f\,0, \dots, f\,(d-1)$ in the residue field of $O$ are algebraically independent over $k$; in particular $\mathrm{ringKrullDim}\, A$ is a positive integer.
--
--   Classically: every non-zero prime of an affine domain over a field — every proper irreducible closed subvariety of an affine variety — is the centre of a prime divisor of the function field, a valuation of $K$ whose residue field has transcendence degree $\dim A - 1$ over $k$; the statement is the algebraic counterpart of blowing up the subvariety and taking a component of the exceptional divisor. It is proved from the dimension formula $\mathrm{ht}(P) + \dim(A/P) = \dim A$ for primes of an affine domain together with the identification of $\mathrm{ringKrullDim}$ with the transcendence degree over $k$, and it is used in the construction of models with divisorial boundary, via [`AlgebraicGeometry.exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper`](thm.html#AlgebraicGeometry.exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem Ideal.exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    ∃ (O : ValuationSubring K) (d : ℕ) (f : Fin d → K),
      O ≠ ⊤ ∧ (∀ a : A, algebraMap A K a ∈ O) ∧
      (∀ a : A, O.valuation (algebraMap A K a) < 1 ↔ a ∈ p) ∧
      ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A ∧
      (∀ i, f i ∈ O) ∧
      ∀ Q : MvPolynomial (Fin d) k, O.valuation (MvPolynomial.aeval f Q) < 1 → Q = 0 := by sorry
