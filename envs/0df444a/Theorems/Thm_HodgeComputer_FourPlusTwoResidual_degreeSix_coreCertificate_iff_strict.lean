-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_degreeSix_coreCertificate_iff_strict
-- name    : HodgeComputer.FourPlusTwoResidual.degreeSix_coreCertificate_iff_strict
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:35.233506+00:00
-- url     : https://prove2.me/theorems/e9e09848-70c4-4d05-b1af-3c6a6342d107
-- title:
--   Degree-six core certificates on four-plus-two-residual normalize to strict divergence-free fields
-- statement:
--   Let $H(x_0, x_1, y_0, y_1)$ denote the homogeneous sextic core polynomial of `four-plus-two-residual`, and let $A = x_0^3 y_0^3$ be the core source. Suppose $D \in \mathbb{C}[x_0, x_1, y_0, y_1]$ is a nonzero homogeneous polynomial of degree $6$ that is relatively prime to $H$.
--
--   Then $D$ admits a twisted core certificate $u = (u_0, u_1, u_2, u_3)$ of homogeneous degree $7$ satisfying
--
--   $$
--   2 A D^2 - 2 D (u \cdot \nabla H) + 3 H \bigl(D \operatorname{div}(u) - u \cdot \nabla D\bigr) = 0
--   $$
--
--   if and only if $D$ admits a **strict divergence-free** homogeneous degree-$7$ vector field $p = (p_0, p_1, p_2, p_3)$ satisfying the decoupled pair of identities
--
--   $$
--   p \cdot \nabla H = A D \qquad \text{and} \qquad D \operatorname{div}(p) - p \cdot \nabla D = 0.
--   $$
--
--   Specifically, because $\deg D = 6 = \deg H$ and $\gcd(H, D) = 1$, divisibility forces $u \cdot \nabla H - A D = H R$ for a homogeneous sextic $R$, and subtracting the Euler multiple $\frac{1}{6} R (x_0, x_1, y_0, y_1)$ simultaneously cancels both the Jacobian remainder $H R$ and the divergence numerator $D \operatorname{div}(u) - u \cdot \nabla D = \frac{2}{3} D R$. This reduces any degree-$6$ search on the four-variable core to the strict Jacobian ideal membership $A D \in J(H)_{12}$ paired with the divergence-free bracket equations.
--
--   **Formalization Note** Variables `0, 1, 2, 3` in `MvPolynomial (Fin 4) ℂ` represent $(x_0, x_1, y_0, y_1)$.
-- source:
--   Hodge.computer GitHub Discussion #120 (`four-plus-two-residual`), observation of `benediamond` (2026-11-18, comment `DC_kwDOVLOOJc4BLIHo`), https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoCore
import Mathlib.RingTheory.Polynomial.UniqueFactorization
open scoped BigOperators

theorem HodgeComputer.FourPlusTwoResidual.degreeSix_coreCertificate_iff_strict
    (D : MvPolynomial (Fin 4) ℂ) (hD_ne : D ≠ 0) (hD_hom : D.IsHomogeneous 6)
    (hD_coprime : IsRelPrime HodgeComputer.FourPlusTwoResidual.core D) :
    (∃ u : Fin 4 → MvPolynomial (Fin 4) ℂ,
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D u) ↔
    (∃ p : Fin 4 → MvPolynomial (Fin 4) ℂ,
      (∀ i, (p i).IsHomogeneous 7) ∧
      (∑ i, MvPolynomial.pderiv i HodgeComputer.FourPlusTwoResidual.core * p i =
        HodgeComputer.FourPlusTwoResidual.coreSource * D) ∧
      (D * (∑ i, MvPolynomial.pderiv i (p i)) -
        ∑ i, MvPolynomial.pderiv i D * p i = 0)) := by sorry
