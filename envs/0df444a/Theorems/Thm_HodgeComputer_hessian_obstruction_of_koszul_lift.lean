-- Prove2me | Theorems.Thm_HodgeComputer_hessian_obstruction_of_koszul_lift
-- name    : HodgeComputer.hessian_obstruction_of_koszul_lift
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T13:09:34.293306+00:00
-- url     : https://prove2.me/theorems/28bf36bc-b463-4a98-95d6-8c488a9c7872
-- title:
--   Jacobian-ring Hessian obstruction for normalized certificate lifts
-- statement:
--   Let \(F\in\mathbb C[Z_0,\ldots,Z_n]\) be homogeneous of positive degree, and write \(J=(\partial_0F,\ldots,\partial_nF)\). Choose polynomials \(A,c_i,U_{ij}\), and set
--   \[
--   D=\sum_i c_i\partial_iF,\qquad
--   N_i=Ac_i+\sum_j(U_{ij}-U_{ji})\partial_jF.
--   \]
--   If \(F\) divides \(D\operatorname{div}N-N(D)\), then
--   \[
--   A\sum_{i,j}c_ic_j\partial_i\partial_jF\in J.
--   \]
--   This necessary condition is independent of all Koszul correction coefficients \(U_{ij}\). It can therefore reject a proposed denominator direction before solving for those corrections. The assertion does not assume that every numerator lift has this form, and it is not a sufficiency criterion for certificates.
-- source:
--   Jacobian-ring obstruction discussed by fqlx in hodge-computer/sextics discussion #125 (24 October 2026), and docs/05-computation.md section 5.2. Generalized here to arbitrary projective dimension and positive homogeneous degree, using the unchanged Prove2Me certificate definitions.

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem HodgeComputer.hessian_obstruction_of_koszul_lift {n : ℕ} {F A : HodgeComputer.AmbientPoly n} {d : ℕ}
    (hF : F.IsHomogeneous d) (hd : 0 < d)
    (c : Fin (n+1) → HodgeComputer.AmbientPoly n)
    (U : Fin (n+1) → Fin (n+1) → HodgeComputer.AmbientPoly n)
    (hres : F ∣ HodgeComputer.divergenceNumerator (HodgeComputer.directional F c)
      (fun i => A*c i + ∑ j, (U i j-U j i)*MvPolynomial.pderiv j F)) :
    A*(∑ i, ∑ j, c i*c j*MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) ∈
      Ideal.span (Set.range (fun i => MvPolynomial.pderiv i F)) := by sorry
