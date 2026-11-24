-- Prove2me | Theorems.Thm_HodgeComputer_Formal_HoldoutCover_hasCertificate_of_normalized
-- name    : HodgeComputer.Formal.HoldoutCover.hasCertificate_of_normalized
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:19:05.121707+00:00
-- url     : https://prove2.me/theorems/d8f35dc3-b49e-4df7-a6d9-fbab300261b3
-- title:
--   Homogeneous certificate from a normalized rational solution
-- statement:
--   Let $F, A, D, Q \in \mathbb{C}[X_0,\dots,X_5]$ and $N : \operatorname{Fin} 6 \to \mathbb{C}[X_0,\dots,X_5]$ satisfy:
--   - $F$ and $A$ are homogeneous of degree $6$, $F$ is prime, and $D$ is relatively prime to $F$;
--   - $\sum_{i=0}^5 (\partial_i F) N_i = A D$ (the normal equation);
--   - $D \sum_{i=0}^5 \partial_i N_i - \sum_{i=0}^5 (\partial_i D) N_i = F Q$ (the cleared divergence equation);
--   - there exists a chart index $i \in \{0,\dots,5\}$ such that $F \nmid \partial_i F$.
--
--   Then $(F, A)$ admits a homogeneous rational Hodge certificate with $(n, d, q) = (5, 6, 1)$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/HoldoutCover/HomogeneousCertificate.lean

import Definitions.Def_DiamondCertificate
import Definitions.Def_HodgeComputerFormal_Algebra
set_option autoImplicit false

theorem HodgeComputer.Formal.HoldoutCover.hasCertificate_of_normalized
    (F A D : HodgeComputer.Sextic.Poly) (N : Fin 6 → HodgeComputer.Sextic.Poly)
    (Q : HodgeComputer.Sextic.Poly)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (hlegal : IsRelPrime F D)
    (normal : HodgeTestbed.directional F N = A * D)
    (divergence : HodgeTestbed.divergenceNumerator D N = F * Q)
    (i : Fin 6) (hchart : ¬ F ∣ MvPolynomial.pderiv i F) :
    HodgeComputer.HasCertificate (n := 5) F A 6 1 := by sorry
