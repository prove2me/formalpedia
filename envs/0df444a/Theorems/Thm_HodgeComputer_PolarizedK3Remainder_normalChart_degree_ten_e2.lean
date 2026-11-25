-- Prove2me | Theorems.Thm_HodgeComputer_PolarizedK3Remainder_normalChart_degree_ten_e2
-- name    : HodgeComputer.PolarizedK3Remainder.normalChart_degree_ten_e2
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T01:50:31.232943+00:00
-- url     : https://prove2.me/theorems/b517a8f8-f896-4141-88c0-d51f13d77f82
-- title:
--   Polarized K3 remainder: residue equation at denominator degree ten
-- statement:
--   For the polarized-k3-remainder instance $(F,A)$ with $q=1$, there exist a homogeneous denominator $S$ of degree exactly $10$, numerator components $W_j$ of degree $11$, and a quotient $Q$, such that $S\neq0$, $\operatorname{IsRelPrime}(F,S)$, and
--
--   $$\operatorname{residue}_{F,A}(S,W)=F\cdot Q.$$
--
--   This is the second normalized equation $E_2$ of the normal chart at the fixed even degree cut. Together with the automatic first normalized equation $E_1$ it yields a degree-ten cleared certificate. Existence is open: the block-swap involution reaches the K3 exterior-square remainder $\Lambda^2 H^2(w^2=f)_{\mathrm{prim}}$ (Chapter 3A §§3A.4–3A.6).
-- source:
--   https://hodge.computer/#case/polarized-k3-remainder ; parallel to RankOneBiquartic.normalChart_degree_ten_e2 ; docs/03a-split-and-k3.md

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.PolarizedK3Remainder

theorem HodgeComputer.PolarizedK3Remainder.normalChart_degree_ten_e2 :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 10 ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous 11) ∧
      NormalChart.residue F A S W = F * Q := by sorry
