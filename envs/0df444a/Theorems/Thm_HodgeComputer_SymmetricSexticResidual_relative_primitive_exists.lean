-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_relative_primitive_exists
-- name    : HodgeComputer.SymmetricSexticResidual.relative_primitive_exists
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:53.482483+00:00
-- url     : https://prove2.me/theorems/03107a27-44a7-4b8d-b3b9-5e0df9b35d76
-- title:
--   Existence of a cleared relative two-form primitive on the reflection cubic for symmetric-sextic-residual
-- statement:
--   For the weighted cubic threefold $f_{\mathrm{sym}}(\lambda, b, c, d, u) = 0$ and descended quadratic source $P_{\mathrm{sym}}(\lambda, b, c, d, u) = b d (1 - u)(c^2 - \lambda^2 u)$ of `symmetric-sextic-residual`, there exist polynomials $D \neq 0$ coprime to $f_{\mathrm{sym}}$, $C_0, C_1, C_2$, and $Q$ in $\mathbb{C}[\lambda, b, c, d, u]$ satisfying the cleared relative-primitive equation
--
--   $$
--   (\partial_u f_{\mathrm{sym}})^2 \sum_{j \in \{b,c,d\}} \Bigl[ (\partial_u f_{\mathrm{sym}}) (D \partial_j C_j - C_j \partial_j D) - (\partial_j f_{\mathrm{sym}})(D \partial_u C_j - C_j \partial_u D) \Bigr] - 2 D^2 \bigl((\partial_u f_{\mathrm{sym}})(\partial_u P_{\mathrm{sym}}) - (\partial_{uu} f_{\mathrm{sym}}) P_{\mathrm{sym}}\bigr) = f_{\mathrm{sym}} Q.
--   $$
--
--   By reflection-chart transport, proving this three-component relative primitive on the affine cubic threefold $f_{\mathrm{sym}} = 0$ suffices to establish the open mission `HodgeComputer.SymmetricSexticResidual.certificate`.
-- source:
--   Hodge.computer Atlas instance `symmetric-sextic-residual`, Chapter 3B and GitHub Discussion #117, https://github.com/hodge-computer/sextics/discussions/117

import Definitions.Def_HodgeComputerSymmetricChart

theorem HodgeComputer.SymmetricSexticResidual.relative_primitive_exists :
    HodgeComputer.ReflectionChart.RelativePrimitive
      HodgeComputer.SymmetricSexticResidual.symWeighted
      HodgeComputer.SymmetricSexticResidual.symSource := by sorry
