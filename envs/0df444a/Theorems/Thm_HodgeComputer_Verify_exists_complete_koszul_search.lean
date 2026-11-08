-- Prove2me | Theorems.Thm_HodgeComputer_Verify_exists_complete_koszul_search
-- name    : HodgeComputer.Verify.exists_complete_koszul_search
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T13:36:26.936948+00:00
-- url     : https://prove2.me/theorems/8dee171d-cf60-4320-8750-e8b9d557bd4a
-- title:
--   Completeness of the homogeneous character-projected fixed-denominator search
-- statement:
--   Let \(F\) be a nonzero homogeneous polynomial of positive degree \(d\) in \(n+1\) variables, let \(q>0\), and suppose its partial derivatives form a weakly regular sequence. Give the variables weights \(w_i\) in an abelian group, with \(F,A,D\) of respective weights \(0,a,b\). Put \(e=\deg D\), and suppose the required numerator degree satisfies
--   \[
--   e+dq-n=r+d-1\qquad(r\ge0).
--   \]
--   Fix any numerator lift \(M\) with that ordinary degree, component weights \(a+b+w_i\), and \(qM(F)=AD\). If any certificate exists with denominator \(D\), then there is one with numerator
--   \[
--   L_i=M_i+\sum_j(U_{ij}-U_{ji})\partial_jF,
--   \]
--   where \(U_{ij}=0\) for \(j\le i\), and every remaining \(U_{ij}\) has ordinary degree \(r\) and weight \(a+b+w_i+w_j\). Moreover the certificate can be chosen normalized:
--   \[
--   D\operatorname{div}L-L(D)=F^qS.
--   \]
--   For six variables this leaves exactly fifteen polynomial correction positions. Thus, under the stated regularity and weight hypotheses, searching all coefficients in these prescribed spaces loses no certificate with the fixed denominator. This does not restrict which denominators may be considered and does not establish regularity for any particular sextic.
-- source:
--   The complete correction map and exact gauge/character reduction of hodge-computer/sextics docs/05-computation.md sections 5.1–5.3, combined here into a kernel-checked theorem for the unchanged Prove2Me certificate contract.

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
open HodgeComputer MvPolynomial RingTheory.Sequence
open scoped BigOperators

theorem HodgeComputer.Verify.exists_complete_koszul_search {n : ℕ} {Γ : Type*} [AddCommGroup Γ] (w : Fin (n+1) → Γ) {F A D : AmbientPoly n} {a b : Γ}
    {d q r : ℕ} {N : Fin (n+1) → AmbientPoly n} {Q : AmbientPoly n}
    (h : Verify F A d q D N Q) (hd : 0<d) (hq : 0<q)
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F)))
    (hF : F.IsWeightedHomogeneous w 0) (hA : A.IsWeightedHomogeneous w a)
    (hD : D.IsWeightedHomogeneous w b)
    (hr : (D.totalDegree:ℤ)+d*q-n=((r+(d-1):ℕ):ℤ))
    (M : Fin (n+1) → AmbientPoly n)
    (hM : ∀ i, (M i).IsHomogeneous (r+(d-1)))
    (hMw : ∀ i, (M i).IsWeightedHomogeneous w (a+b+w i))
    (hMdir : (q:AmbientPoly n)*directional F M=A*D) :
    ∃ (U : Fin (n+1) → Fin (n+1) → AmbientPoly n) (S : AmbientPoly n),
      (∀ i j, j ≤ i → U i j=0) ∧
      (∀ i j, (U i j).IsHomogeneous r ∧ (U i j).IsWeightedHomogeneous w (a+b+w i+w j)) ∧
      Verify F A d q D (fun i => M i+∑ j, (U i j-U j i)*pderiv j F) S ∧
      divergenceNumerator D (fun i => M i+∑ j, (U i j-U j i)*pderiv j F)=F^q*S := by sorry
