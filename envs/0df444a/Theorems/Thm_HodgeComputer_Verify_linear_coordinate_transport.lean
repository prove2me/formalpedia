-- Prove2me | Theorems.Thm_HodgeComputer_Verify_linear_coordinate_transport
-- name    : HodgeComputer.Verify.linear_coordinate_transport
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T15:25:15.725702+00:00
-- url     : https://prove2.me/theorems/5da53f90-58c4-4578-9af2-b23f3b980b05
-- title:
--   Polynomial certificate transport under every invertible linear coordinate change
-- statement:
--   Let \((D,N,Q)\) be a polynomial certificate for \((F,A,d,q)\), and let \(B\in\operatorname{GL}_{n+1}(\mathbb C)\) have inverse \(R\). Define \(T_B(P)(z)=P(Bz)\). Then
--   \[
--   D'=T_B(D),\qquad N'=R\,T_B(N),\qquad Q'=T_B(Q)
--   \]
--   give a certificate for \((T_B(F),T_B(A),d,q)\). The theorem verifies the full defect equation, the required integer homogeneity, nonvanishing, and relative primality of the transformed denominator. Thus any invertible linear change of coordinates transports a certificate, with the inverse matrix acting on the vector-field components.
-- source:
--   Polynomial chain rule, invariance of matrix trace under conjugation, and invertible substitution. Extends the signed/permutation transport setting of hodge-computer CoordinateChanges.lean, credited there to fqlx (#123) and benediamond (#153). https://github.com/hodge-computer/sextics/blob/2d60d08d25fba3e02162b39d4c50f6b467e7f506/formal/lean/HodgeComputer/CoordinateChanges.lean

import Definitions.Def_DiamondCertificate
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
open scoped BigOperators

theorem HodgeComputer.Verify.linear_coordinate_transport {n d q : ℕ}
    (B R : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hBR : B*R=1) (hRB : R*B=1)
    {F A D Q : HodgeComputer.AmbientPoly n}
    {N : Fin (n+1) → HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q) :
    let T : HodgeComputer.AmbientPoly n →+* HodgeComputer.AmbientPoly n :=
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i : Fin (n+1) => ∑ j, MvPolynomial.C (B i j)*MvPolynomial.X j)
    HodgeComputer.Verify (T F) (T A) d q (T D)
      (fun i => ∑ j, MvPolynomial.C (R i j)*T (N j)) (T Q) := by sorry
