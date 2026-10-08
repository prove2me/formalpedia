-- Prove2me | Theorems.Thm_GoldbachPrimalityCertificate_lucas_from_prime_list
-- name    : GoldbachPrimalityCertificate.lucas_from_prime_list
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T00:56:31.127621+00:00
-- url     : https://prove2.me/theorems/65d6d1cd-83e0-4f65-b5e6-439a59c72a95
-- title:
--   A finite prime-factor-list interface for Lucas primality certificates
-- statement:
--   This is a finite-factor-list interface to Mathlib's existing Lucas primality
--   theorem. Suppose a list of proved primes has product `p - 1`, and an element
--   `a` modulo `p` satisfies `a^(p-1) = 1` while `a^((p-1)/r) ≠ 1` for every listed
--   factor `r`. Then `p` is prime. Repeated factors are allowed.
--
--   The proof establishes that every prime dividing the product occurs in the list:
--   induction uses the prime-divides-product property, followed by equality of two
--   primes when one divides the other. The list conditions therefore provide all
--   the hypotheses of `lucas_primality`.
--
--   This wrapper is intended for explicit generated certificates, whose factor
--   primalities and modular equalities are proved in Lean. Factorizations and modular
--   answers produced by a search program are not trusted. The mathematical
--   primality criterion is the known Lucas/Pratt method, already present in Mathlib;
--   the contribution is a reusable finite-data interface.
-- source:
--   Checkable computational certificates for the finite Goldbach input in https://arxiv.org/abs/1201.6656; method, exact coverage and performance evidence in the statement.

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Algebra.BigOperators.Group.List.Defs
set_option autoImplicit false

theorem GoldbachPrimalityCertificate.lucas_from_prime_list (p : ℕ) (a : ZMod p) (factors : List ℕ)
    (hp : ∀ r ∈ factors, Nat.Prime r) (hprod : factors.prod = p - 1)
    (ha : a ^ (p - 1) = 1)
    (hd : ∀ r ∈ factors, a ^ ((p - 1) / r) ≠ 1) : Nat.Prime p := by sorry
