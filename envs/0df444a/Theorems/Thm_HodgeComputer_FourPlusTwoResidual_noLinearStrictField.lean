-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_noLinearStrictField
-- name    : HodgeComputer.FourPlusTwoResidual.noLinearStrictField
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:57:23.801202+00:00
-- url     : https://prove2.me/theorems/33bbe514-c080-466c-b7ae-d9cf97b7b763
-- title:
--   No linear field solves the four-plus-two cancelled strict core identity
-- statement:
--   Let $H\in\mathbb{C}[x_0,x_1,x_2,x_3]$ be the four-variable core sextic of the Hodge Computer instance four-plus-two-residual, and let $A=x_0^3x_2^3$ be the corresponding core source, as published in `Definitions.Def_HodgeComputerFourPlusTwoCore` (id `85cd56fc-ecf1-4928-8c0f-75b19b944ecb`). Explicitly,
--
--   $$
--   \begin{aligned}
--   H &= x_0^6 + \tfrac57 x_0^5x_1 + \tfrac57 x_0^3x_1x_2x_3 + \tfrac{10}{7}x_0x_1^5 + \tfrac{10}{7}x_0x_1x_2^3x_3 \\
--   &\qquad + x_1^6 + x_2^6 + \tfrac57 x_2^5x_3 + \tfrac{15}{7}x_2x_3^5 + x_3^6, \\
--   A &= x_0^3x_2^3.
--   \end{aligned}
--   $$
--
--   **Claim.** There do not exist linear forms $L_0,\dots,L_3\in\mathbb{C}[x_0,x_1,x_2,x_3]$ (that is, polynomials that are homogeneous of degree $1$) satisfying the cancelled strict core identity
--
--   $$
--   2A - 2\sum_{i=0}^{3}\frac{\partial H}{\partial x_i}\,L_i + 3H\cdot\operatorname{div}(L) = 0,
--   $$
--
--   where $\operatorname{div}(L)=\sum_{i=0}^{3}\partial L_i/\partial x_i$.
--
--   Equivalently, there is no `CoreCertificate` of the form $N_i=D\,L_i$ with each $L_i$ homogeneous of degree $1$. In the integral domain $\mathbb{C}[x_0,x_1,x_2,x_3]$, the factor $D^2$ appearing in the core-certificate identity cancels, and the resulting equation is precisely the displayed identity.
--
--   This lemma rules out one concrete ansatz — a linear field $N_i=D L_i$ — as a construction of a solution to the still-open problem `HodgeComputer.FourPlusTwoResidual.coreCertificate` (id `9fb47380-f045-4b39-825f-3a61dac79c73`). It does not produce a core certificate, and it does not prove `coreCertificate`, `HodgeComputer.FourPlusTwoResidual.normalChart_residue_solvable`, or the mission goal `HodgeComputer.FourPlusTwoResidual.certificate`. Those statements remain open. The already-accepted reduction of the mission goal to `coreCertificate` (including the defect-zero lift) is due to xuanji's sketch and is not revisited here.
--
--   **Formalization Note.** The formal statement is the non-existence of a map $L\colon\mathrm{Fin}\,4\to\mathbb{C}[x_0,x_1,x_2,x_3]$ such that every $L_i$ is homogeneous of degree $1$ and the cancelled identity holds, with $H=$ `core` and $A=$ `coreSource`.
-- source:
--   Official definition HodgeComputerFourPlusTwoCore (prove2.me definition id 85cd56fc-ecf1-4928-8c0f-75b19b944ecb; core and coreSource as used by HodgeComputer.FourPlusTwoResidual.coreCertificate). Instance four-plus-two-residual of Hodge Computer, https://hodge.computer/#case/four-plus-two-residual and github.com/hodge-computer/sextics (data/four-plus-two-residual/instance.rec). The linear-field obstruction was derived from analysis by a better model, relayed by Ethan Cheung, and checked and formalized here. This is not a re-upload of xuanji's accepted sketch of the main certificate (submission a963c410-7abf-4947-a8a6-6f0243b839cf).

import Definitions.Def_HodgeComputerFourPlusTwoCore
open MvPolynomial
open HodgeComputer.FourPlusTwoResidual

theorem HodgeComputer.FourPlusTwoResidual.noLinearStrictField :
    ¬ ∃ L : Fin 4 → MvPolynomial (Fin 4) ℂ,
      (∀ i, (L i).IsHomogeneous 1) ∧
      2 * coreSource - 2 * (∑ i, pderiv i core * L i)
        + 3 * core * (∑ i, pderiv i (L i)) = 0 := by sorry
