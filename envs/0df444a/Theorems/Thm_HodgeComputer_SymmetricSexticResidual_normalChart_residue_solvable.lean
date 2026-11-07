-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_normalChart_residue_solvable
-- name    : HodgeComputer.SymmetricSexticResidual.normalChart_residue_solvable
-- status  : Open
-- author  : @shivm
-- created : 2026-11-07T03:51:38.523212+00:00
-- url     : https://prove2.me/theorems/68e58e98-63ec-4af1-8bca-b66ef4f55b9f
-- title:
--   Symmetric sextic residual: solve the scalar normal-chart residue equation
-- statement:
--   For exactly the sextic $F$ and source $A$ of the symmetric-sextic-residual instance, put $q=1$ and $B=A/q$. There exist complex polynomials $S,W_1,\ldots,W_5,Q$ with $S\ne0$, $S$ homogeneous of degree $e=\deg S$, $\operatorname{IsRelPrime}(F,S)$, and every $W_j$ homogeneous of degree $e+1$, such that
--
--   $$\mathcal R_{F,B}(S,W)=F^qQ.$$
--
--   Here $P=\partial_0F$, $F_j=\partial_jF$, subscripts denote partial derivatives, and
--
--   $$\mathcal R_{F,B}(S,W)=S^2(PB_0-BP_0)+\sum_{j=1}^5\left[P^2S\,\partial_jW_j-PSF_j\,\partial_0W_j+\bigl(F_j(SP_0+PS_0)-P(SP_j+PS_j)\bigr)W_j\right].$$
--
--   The denominator degree has no upper bound, and $Q$ may be nonzero. For each fixed $S$, this is a linear coefficient equation for $W_j$ and $Q$. Choosing a legal $S$ remains part of the problem. Together with the independently proved normal-derivative coprimality and certificate-construction lemmas, this assertion implies the original mission target. It is an explicitly open derived subproblem; the source does not supply a certificate for this instance.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/symmetric-sextic-residual/instance.rec; docs/01-certificates.md, normalized equations E1 and E2. Derived open scalar subproblem for the exact original target.

import Definitions.Def_HodgeComputerSymmetricSexticResidual
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.SymmetricSexticResidual

theorem HodgeComputer.SymmetricSexticResidual.normalChart_residue_solvable :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      NormalChart.residue F A S W = F * Q := by sorry
