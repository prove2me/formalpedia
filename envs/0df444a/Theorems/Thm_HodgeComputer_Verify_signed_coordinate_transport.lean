-- Prove2me | Theorems.Thm_HodgeComputer_Verify_signed_coordinate_transport
-- name    : HodgeComputer.Verify.signed_coordinate_transport
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T15:10:34.833172+00:00
-- url     : https://prove2.me/theorems/be9b7f88-8da6-4d8d-803a-f2d43fe9796d
-- title:
--   Transport of polynomial certificates through signed coordinate permutations
-- statement:
--   Let \((D,N,Q)\) be a polynomial certificate for \((F,A,d,q)\). Permute the \(n+1\) coordinate variables by \(e\), and then multiply each coordinate \(z_i\) by a complex scalar \(s_i\) satisfying \(s_i^2=1\). Write \(T\) for the resulting polynomial substitution. Then
--   \[
--   D'=T(D),\qquad N'_i=s_i\,T(N_{e^{-1}(i)}),\qquad Q'=T(Q)
--   \]
--   form a certificate for \((T(F),T(A),d,q)\). The theorem preserves exact homogeneity, denominator legality, and the full defect identity, including nonzero remainders. It supplies a verified way to move constructions among signed permutations of the coordinates.
-- source:
--   Adapted from hodge-computer CoordinateChanges.lean (Apache-2.0), commit 2d60d08d25fba3e02162b39d4c50f6b467e7f506. The upstream source credits fqlx (#123) for sign transport and benediamond (#153) for permutations. https://github.com/hodge-computer/sextics/blob/2d60d08d25fba3e02162b39d4c50f6b467e7f506/formal/lean/HodgeComputer/CoordinateChanges.lean

import Definitions.Def_DiamondCertificate
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

theorem HodgeComputer.Verify.signed_coordinate_transport {n d q : ℕ} (e : Fin (n+1) ≃ Fin (n+1))
    (s : Fin (n+1) → ℂ) (hs : ∀ i, s i*s i=1)
    {F A D Q : HodgeComputer.AmbientPoly n}
    {N : Fin (n+1) → HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q) :
    let T : HodgeComputer.AmbientPoly n →+* HodgeComputer.AmbientPoly n :=
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i : Fin (n+1) => MvPolynomial.C (s i)*MvPolynomial.X i)
    HodgeComputer.Verify (T (MvPolynomial.rename e F)) (T (MvPolynomial.rename e A)) d q
      (T (MvPolynomial.rename e D))
      (fun i => MvPolynomial.C (s i)*T (MvPolynomial.rename e (N (e.symm i))))
      (T (MvPolynomial.rename e Q)) := by sorry
