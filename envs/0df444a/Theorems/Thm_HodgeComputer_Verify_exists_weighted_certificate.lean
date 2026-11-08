-- Prove2me | Theorems.Thm_HodgeComputer_Verify_exists_weighted_certificate
-- name    : HodgeComputer.Verify.exists_weighted_certificate
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T13:31:08.213193+00:00
-- url     : https://prove2.me/theorems/65073b6b-8cb0-43d3-962f-78f5a1cf1eeb
-- title:
--   Lossless character projection of rational-vector-field certificates
-- statement:
--   Give each variable \(Z_i\) a weight \(w_i\) in an arbitrary abelian group \(\Gamma\). Suppose \(F,A,D\) have weights \(0,a,b\), respectively. If \((D,N,Q)\) is a valid rational-vector-field certificate, then there is a certificate \((D,M,S)\) with the same denominator and
--   \[
--   \operatorname{wt}(M_i)=a+b+w_i,\qquad \operatorname{wt}(S)=a+2b.
--   \]
--   All ordinary degree bounds and the denominator's legality are preserved. Taking \(\Gamma\) to be a product of cyclic groups gives simultaneous character projection for diagonal root-of-unity symmetries; taking \(\Gamma=\mathbb Z/2\mathbb Z\) gives parity projection. The denominator is required to have a single weight; the theorem does not impose additional invariance on a variable denominator.
-- source:
--   The standard symmetry/averaging reduction in hodge-computer/sextics docs/01-certificates.md and docs/05-computation.md. This proof realizes the reduction directly through abelian-group-graded monomial projections, using the existing Prove2Me certificate contract.

import Definitions.Def_DiamondCertificate
import Mathlib.Tactic.Abel

theorem HodgeComputer.Verify.exists_weighted_certificate {n : ℕ} {Γ : Type*} [AddCommGroup Γ]
    (w : Fin (n+1) → Γ) {F A D : HodgeComputer.AmbientPoly n} {a b : Γ}
    {d q : ℕ} {N : Fin (n+1) → HodgeComputer.AmbientPoly n} {Q : HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q)
    (hF : F.IsWeightedHomogeneous w 0) (hA : A.IsWeightedHomogeneous w a)
    (hD : D.IsWeightedHomogeneous w b) :
    ∃ (M : Fin (n+1) → HodgeComputer.AmbientPoly n) (S : HodgeComputer.AmbientPoly n),
      HodgeComputer.Verify F A d q D M S ∧
      (∀ i, (M i).IsWeightedHomogeneous w (a+b+w i)) ∧
      S.IsWeightedHomogeneous w (a+b+b) := by sorry
