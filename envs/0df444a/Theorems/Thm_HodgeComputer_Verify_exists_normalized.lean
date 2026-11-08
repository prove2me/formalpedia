-- Prove2me | Theorems.Thm_HodgeComputer_Verify_exists_normalized
-- name    : HodgeComputer.Verify.exists_normalized
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T13:01:17.342249+00:00
-- url     : https://prove2.me/theorems/185e23b5-21c9-41b7-aab9-aa298de87bff
-- title:
--   Lossless Euler normalization of every rational-vector-field certificate
-- statement:
--   Let \(F\) be a nonzero homogeneous polynomial of positive degree \(d\) on \(\mathbb C^{n+1}\), and let \(q>0\). Suppose \((D,N,Q)\) is a rational-vector-field certificate for a homogeneous target \(A\), in the sense of the cleared identity
--   \[
--   AD^2-qD\sum_i N_i\partial_iF
--    +F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^{q+1}Q,
--   \]
--   with the certificate's homogeneity conditions and \(\gcd(F,D)=1\).
--
--   Then there is a numerator tuple \(M\), with the same component degrees, for which \((D,M,Q)\) remains a certificate and
--   \[
--   q\sum_i M_i\partial_iF=AD,
--   \qquad
--   D\sum_i\partial_iM_i-\sum_iM_i\partial_iD=F^qQ.
--   \]
--   Thus the normalized equations impose no additional restriction on certificate existence. Both the denominator and the cleared quotient remain unchanged. The theorem applies in every projective dimension and at every positive pole order.
-- source:
--   Euler normalization as described in hodge-computer/sextics, docs/01-certificates.md (Euler freedom and denominator gauges), together with the unchanged Prove2Me Definitions.Def_DiamondCertificate contract.

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

theorem HodgeComputer.Verify.exists_normalized {n : ℕ} {F A D : HodgeComputer.AmbientPoly n} {d q : ℕ}
    {N : Fin (n+1) → HodgeComputer.AmbientPoly n} {Q : HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q) (hd : 0<d) (hq : 0<q) :
    ∃ M : Fin (n+1) → HodgeComputer.AmbientPoly n,
      HodgeComputer.Verify F A d q D M Q ∧
      (q:HodgeComputer.AmbientPoly n)*HodgeComputer.directional F M=A*D ∧
      HodgeComputer.divergenceNumerator D M=F^q*Q := by sorry
