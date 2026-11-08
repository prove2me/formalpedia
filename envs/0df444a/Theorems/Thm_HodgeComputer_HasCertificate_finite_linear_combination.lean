-- Prove2me | Theorems.Thm_HodgeComputer_HasCertificate_finite_linear_combination
-- name    : HodgeComputer.HasCertificate.finite_linear_combination
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T15:07:41.535048+00:00
-- url     : https://prove2.me/theorems/fd55d187-3dab-404c-9cf5-5c1dec0e9335
-- title:
--   Finite linear combinations of certificate sources admit a common-denominator certificate
-- statement:
--   Fix a nonzero homogeneous polynomial \(F\) of degree \(d\) in \(n+1\) variables and a pole parameter \(q\). Let \(I\) be a finite index set, and suppose each source polynomial \(A_i\) has a certificate for this same \(F,d,q\). Then, for arbitrary complex coefficients \(c_i\),
--   \[
--   \sum_{i\in I}c_iA_i
--   \]
--   also has a certificate. The summands may have different denominators and nonzero quotient remainders. Taking products of their legal denominators gives a common denominator, so separately constructed target directions can be combined without a common support hypothesis. The empty family is included.
-- source:
--   Adapted from hodge-computer CertificateOperations.lean (Apache-2.0), commit 2d60d08d25fba3e02162b39d4c50f6b467e7f506; the upstream source credits fqlx, holdout-bundle PR #161, and the accepted one-reflection addition formula. https://github.com/hodge-computer/sextics/blob/2d60d08d25fba3e02162b39d4c50f6b467e7f506/formal/lean/HodgeComputer/CertificateOperations.lean

import Definitions.Def_DiamondCertificate
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
open scoped BigOperators

universe u

theorem HodgeComputer.HasCertificate.finite_linear_combination {n d q : ℕ} {ι : Type u} [Fintype ι]
    (F : HodgeComputer.AmbientPoly n) (hF : F ≠ 0) (hd : F.IsHomogeneous d)
    (A : ι → HodgeComputer.AmbientPoly n) (c : ι → ℂ)
    (h : ∀ i, HodgeComputer.HasCertificate F (A i) d q) :
    HodgeComputer.HasCertificate F (∑ i, MvPolynomial.C (c i)*A i) d q := by sorry
