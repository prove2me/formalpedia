-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_of_ungraded
-- name    : HodgeComputer.FourPlusTwoResidual.coreCertificate_of_ungraded
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T21:02:20.121698+00:00
-- url     : https://prove2.me/theorems/268cb27b-1932-4ee2-aa46-7c46f3dd6d61
-- title:
--   Homogeneous extraction from any cleared polynomial identity for the four-plus-two core
-- statement:
--   Let $H$ be the literal four-variable coupled sextic, $A=x_0^3 y_0^3$, and write $\nabla H\cdot N=\sum_i(\partial_iH)N_i$. Suppose arbitrary complex polynomials $D\ne0,N_0,\ldots,N_3$ satisfy
--   $$2AD^2-2D(\nabla H\cdot N)+3H(D\,\operatorname{div}N-\nabla D\cdot N)=0.$$
--   Then the existing predicate `HodgeComputer.FourPlusTwoResidual.CoreCertificate` holds for some homogeneous denominator of positive degree and four homogeneous numerators of one higher degree. This lets a computation use ungraded polynomials, including denominators with nonzero constant term.
-- source:
--   Hodge Computer four-plus-two-residual, GitHub Discussion #120; Phase 4 finite geometric-sum construction. Shared homogeneous-component calculus adapted from the holdout construction by fqlx. https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoCore

theorem HodgeComputer.FourPlusTwoResidual.coreCertificate_of_ungraded
    (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ) (hD : D ≠ 0)
    (hraw : 2 * HodgeComputer.FourPlusTwoResidual.coreSource * D ^ 2 - 2 * D * (∑ i, MvPolynomial.pderiv i HodgeComputer.FourPlusTwoResidual.core * N i)
      + 3 * HodgeComputer.FourPlusTwoResidual.core * (D * (∑ i, MvPolynomial.pderiv i (N i)) - ∑ i, MvPolynomial.pderiv i D * N i) = 0) :
    ∃ (T : MvPolynomial (Fin 4) ℂ) (M : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.CoreCertificate T M := by sorry
