-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate
-- name    : HodgeComputer.FourPlusTwoResidual.coreCertificate
-- status  : Open
-- author  : @xuanji
-- created : 2026-11-10T05:25:43.605883+00:00
-- url     : https://prove2.me/theorems/9fb47380-f045-4b39-825f-3a61dac79c73
-- title:
--   Four plus two: strict four-variable core certificate
-- statement:
--   Let $H\in\mathbb{C}[x_0,x_1,x_2,x_3]$ be the sextic
--   $$H = x_0^6 + \tfrac57 x_0^5x_1 + \tfrac57 x_0^3x_1x_2x_3 + \tfrac{10}{7}x_0x_1^5 + \tfrac{10}{7}x_0x_1x_2^3x_3 + x_1^6 + x_2^6 + \tfrac57 x_2^5x_3 + \tfrac{15}{7}x_2x_3^5 + x_3^6$$
--   and let $A=x_0^3x_2^3$.
--
--   **Claim.** There exist a nonzero homogeneous polynomial $D$ of some degree $k+1\ge 1$ and homogeneous polynomials $N_0,\dots,N_3$ of degree $k+2$ such that
--   $$2\,A\,D^2 \;-\; 2\,D\sum_{i=0}^{3}\frac{\partial H}{\partial x_i}N_i \;+\; 3\,H\Big(D\sum_{i=0}^{3}\frac{\partial N_i}{\partial x_i}-\sum_{i=0}^{3}\frac{\partial D}{\partial x_i}N_i\Big)=0 .$$
--   In other words, the degree-one rational vector field $v=\sum_i (N_i/D)\partial_{x_i}$ on $\mathbb{C}^4$ solves
--   $$v(H)-\tfrac32\,H\,\operatorname{div} v = A$$
--   exactly, with no error term. The denominator $D$ is unrestricted; in particular it may be divisible by $H$.
--
--   This is the four-variable core of the Hodge Computer instance `four-plus-two-residual`, whose polynomial is $F=H(X_0,X_1,Y_0,Y_1)+B(X_2,Y_2)$ with source $X_0^3Y_0^3$ and pole parameter $q=1$. A solution $(D,N)$ lifts to a Diamond certificate for that instance with denominator $4D^2$ (this lift is formally verified in the sketch for `HodgeComputer.FourPlusTwoResidual.certificate`). Geometrically the claim says that the class of $A\,dx/u^5$ in $H^3$ of the Calabi–Yau threefold $T_H=\{u^3=H\}\subset\mathbb{P}(1,1,1,1,2)$, which is anti-invariant under $(x_2,x_3)\mapsto(-x_2,-x_3)$, vanishes on the complement of a divisor. That statement is asserted on paper by the weighted threefold theorem of the Hodge Computer documentation (Chapter 3B), so a solution is expected to exist, but no explicit $(D,N)$ is known and the degree may be large.
--
--   **Formalization Note.** The statement is `∃ D N, HodgeComputer.FourPlusTwoResidual.CoreCertificate D N` over `MvPolynomial (Fin 4) ℂ`, with `CoreCertificate` from `Definitions.Def_HodgeComputerFourPlusTwoCore`.
-- source:
--   Hodge Computer, instance four-plus-two-residual, https://hodge.computer and github.com/hodge-computer/sextics (data/four-plus-two-residual/instance.rec; docs/03b-weighted-threefolds.md, weighted threefold theorem, for the expected existence). The four-variable form is a reduction of prove2.me theorem HodgeComputer.FourPlusTwoResidual.certificate.

import Definitions.Def_HodgeComputerFourPlusTwoCore

theorem HodgeComputer.FourPlusTwoResidual.coreCertificate :
    ∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D N := by sorry
