-- Prove2me | Theorems.Thm_HodgeComputer_Verify_exists_involution_averaged_certificate
-- name    : HodgeComputer.Verify.exists_involution_averaged_certificate
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T15:49:03.43209+00:00
-- url     : https://prove2.me/theorems/b87cf21b-4252-4058-86a5-b4dc6203156d
-- title:
--   Averaging certificates with an invariant denominator under a sign involution
-- statement:
--   Let \(T\) be the substitution \(z_i\mapsto s_i z_i\), where \(s_i^2=1\), and assume \(T(F)=F\) and \(T(A)=-A\). From any certificate \((D,N,Q)\) for \((F,A,d,q)\), there exist \(M,R\) such that
--   \[
--   \bigl(D\,T(D),M,R\bigr)
--   \]
--   is a certificate for the same source and pole parameter, and
--   \[
--   T(D\,T(D))=D\,T(D),\qquad T(M_i)=-s_iM_i,\qquad T(R)=-R.
--   \]
--   Thus an arbitrary legal denominator can be replaced by an invariant one while imposing the source's anti-invariant component parities. The denominator is allowed to change; this does not assert that a fixed non-invariant denominator admits such a projection.
-- source:
--   Two-element Reynolds averaging, denominator norm D*T(D), and the certificate addition and sign-transport formulas. Upstream sign transport is credited to fqlx (#123), and addition to fqlx (#161) and the one-reflection construction: https://github.com/hodge-computer/sextics/tree/2d60d08d25fba3e02162b39d4c50f6b467e7f506/formal/lean/HodgeComputer

import Definitions.Def_DiamondCertificate
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
open scoped BigOperators

theorem HodgeComputer.Verify.exists_involution_averaged_certificate {n d q : ℕ}
    (s : Fin (n+1) → ℂ) (hs : ∀ i, s i*s i=1)
    {F A D Q : HodgeComputer.AmbientPoly n}
    {N : Fin (n+1) → HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q) :
    let T : HodgeComputer.AmbientPoly n →+* HodgeComputer.AmbientPoly n :=
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i : Fin (n+1) => MvPolynomial.C (s i)*MvPolynomial.X i)
    T F=F → T A= -A →
      ∃ (M : Fin (n+1) → HodgeComputer.AmbientPoly n) (R : HodgeComputer.AmbientPoly n),
        HodgeComputer.Verify F A d q (D*T D) M R ∧ T (D*T D)=D*T D ∧
        (∀ i, T (M i)= -MvPolynomial.C (s i)*M i) ∧ T R= -R := by sorry
