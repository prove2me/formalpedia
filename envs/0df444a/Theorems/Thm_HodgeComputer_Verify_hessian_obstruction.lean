-- Prove2me | Theorems.Thm_HodgeComputer_Verify_hessian_obstruction
-- name    : HodgeComputer.Verify.hessian_obstruction
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T13:19:56.68203+00:00
-- url     : https://prove2.me/theorems/e173c0a8-8eae-48c7-b13e-a2cd89470383
-- title:
--   Necessary Jacobian-ring obstruction for every certificate with a Jacobian denominator
-- statement:
--   Let \(F\in\mathbb C[Z_0,\ldots,Z_n]\) have positive homogeneous degree \(d\), let \(q>0\), and suppose its ordered partial derivatives form a weakly regular sequence. Write \(J=(\partial_0F,\ldots,\partial_nF)\). Choose polynomials \(c_i\), and set
--   \[
--   D=\sum_i c_i\partial_iF.
--   \]
--   If \((D,N,Q)\) is any valid rational-vector-field certificate for \(A\) at pole order \(q\), in the existing Prove2Me certificate contract, then
--   \[
--   A\sum_{i,j}c_ic_j\partial_i\partial_jF\in J.
--   \]
--   The numerator need not initially be normalized or presented by Koszul corrections. Thus failure of this ideal-membership condition rules out every certificate with this denominator, under the stated regularity hypothesis.
-- source:
--   Combines Euler normalization, the first-syzygy theorem for a regular sequence, and the Jacobian-ring Hessian obstruction discussed by fqlx in hodge-computer/sextics discussion #125 and docs/05-computation.md section 5.2.

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

theorem HodgeComputer.Verify.hessian_obstruction {n : ℕ} {F A : HodgeComputer.AmbientPoly n} {d q : ℕ}
    (c N : Fin (n+1) → HodgeComputer.AmbientPoly n) (Q : HodgeComputer.AmbientPoly n)
    (h : HodgeComputer.Verify F A d q (HodgeComputer.directional F c) N Q)
    (hd : 0<d) (hq : 0<q)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (HodgeComputer.AmbientPoly n)
      (List.ofFn (fun i => MvPolynomial.pderiv i F))) :
    A*(∑ i, ∑ j, c i*c j*MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) ∈
      Ideal.span (Set.range (fun i => MvPolynomial.pderiv i F)) := by sorry
