-- Prove2me | Theorems.Thm_HodgeComputer_PolarizedK3Remainder_normalChart_degree_ten_witness
-- name    : HodgeComputer.PolarizedK3Remainder.normalChart_degree_ten_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:56:36.761506+00:00
-- url     : https://prove2.me/theorems/04c8bba5-d7d3-4d48-b146-ce2d7d6e2ffd
-- title:
--   Polarized K3 remainder: normal-chart certificate at denominator degree ten
-- statement:
--   For the polarized-k3-remainder instance $(F,A)$ with $q=1$, there exist a homogeneous denominator $S$ of degree exactly $10$, numerator components $W_j$ homogeneous of degree $11$, and a quotient $Q$, such that $S\neq 0$, $\operatorname{IsRelPrime}(F,S)$, and
--
--   $$\operatorname{defect}\bigl(F,A,PS,1,N\bigr)=F^{2}Q$$
--
--   with the normal-chart numerator $N$ built from $(S,W)$. This is the certificate problem specialized to a single even denominator degree (the same degree cut used for the rank-one-biquartic parallel). Existence at this degree is not supplied by the block-sign or elliptic-companion theorems: the target reaches the K3 exterior-square remainder $\Lambda^2 H^2(w^2=f)_{\mathrm{prim}}$ (Chapter 3A §§3A.4–3A.6).
-- source:
--   https://hodge.computer/#case/polarized-k3-remainder ; https://github.com/hodge-computer/sextics/blob/main/data/polarized-k3-remainder/why.md ; parallel to RankOneBiquartic.normalChart_degree_ten_witness

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.PolarizedK3Remainder

theorem HodgeComputer.PolarizedK3Remainder.normalChart_degree_ten_witness :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 10 ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous 11) ∧
      defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W) = F ^ 2 * Q := by sorry
