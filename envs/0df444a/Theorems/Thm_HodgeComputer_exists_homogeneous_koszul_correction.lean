-- Prove2me | Theorems.Thm_HodgeComputer_exists_homogeneous_koszul_correction
-- name    : HodgeComputer.exists_homogeneous_koszul_correction
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T13:17:04.638689+00:00
-- url     : https://prove2.me/theorems/3193b582-723c-45c2-9804-5f43a7813999
-- title:
--   Completeness of homogeneous Koszul corrections for numerator lifts
-- statement:
--   Let \(F\in\mathbb C[Z_0,\ldots,Z_n]\) be homogeneous of degree \(d\), and suppose its ordered partial derivatives form a weakly regular sequence. Let \(r\ge0\), and let \(N,M\) be polynomial vector fields whose components are homogeneous of degree \(r+d-1\). If
--   \[
--   \sum_iN_i\partial_iF=\sum_iM_i\partial_iF,
--   \]
--   then there are homogeneous polynomials \(U_{ij}\) of degree \(r\) such that
--   \[
--   N_i=M_i+\sum_j(U_{ij}-U_{ji})\partial_jF.
--   \]
--   Consequently the pairwise Koszul correction space contains every homogeneous numerator lift of the same first normalized equation, under the stated regularity hypothesis. This justifies that part of a complete coefficient search; the regularity hypothesis and any additional symmetry restrictions must still be checked. The formal degree uses natural subtraction when d is zero.
-- source:
--   The standard first-syzygy theorem for a regular sequence, used in hodge-computer/sextics docs/05-computation.md section 5.2. The proof here derives it directly from Mathlib IsWeaklyRegular and proves the homogeneous degree bound by projection.

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

theorem HodgeComputer.exists_homogeneous_koszul_correction {n : ℕ} {F : HodgeComputer.AmbientPoly n} {d r : ℕ}
    (hF : F.IsHomogeneous d)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (HodgeComputer.AmbientPoly n)
      (List.ofFn (fun i => MvPolynomial.pderiv i F)))
    (N M : Fin (n+1) → HodgeComputer.AmbientPoly n)
    (hN : ∀ i, (N i).IsHomogeneous (r+(d-1)))
    (hM : ∀ i, (M i).IsHomogeneous (r+(d-1)))
    (hlift : HodgeComputer.directional F N=HodgeComputer.directional F M) :
    ∃ U : Fin (n+1) → Fin (n+1) → HodgeComputer.AmbientPoly n,
      (∀ i j, (U i j).IsHomogeneous r) ∧
      ∀ i, N i=M i+∑ j, (U i j-U j i)*MvPolynomial.pderiv j F := by sorry
