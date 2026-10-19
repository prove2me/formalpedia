-- Prove2me | Theorems.Thm_MCSustain_WinWin_impact_Hup_vs_Hu
-- name    : MCSustain.WinWin.impact_Hup_vs_Hu
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:29.92733+00:00
-- url     : https://prove2.me/theorems/d18c586f-cac8-4b4f-b528-5867891cb3ab
-- title:
--   Proof of Proposition 3, p. a7 (PDF 39), case 1) — E[I_ℍ'u − I_ℍu] formula, and it is < 0 iff E_l/E_s > R
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   Write $n_H=\mu t\lambda_H^2/(4f)$ and $n'_H=\mu t\lambda_H'^2/(4f)$ for the varieties of $\mathbb H_u$ and $\mathbb H'_u$. The expected impact of the hybrid solution $\mathbb H'_u$ minus that of the MP solution $\mathbb H_u$ is
--   $$\mathbb E[I_{\mathbb H'_u}]-\mathbb E[I_{\mathbb H_u}]=E_s\mu(1-n_H\lambda_H)-E_l(m_H-\mu)(n_H\lambda_H-n'_H\lambda'_H),$$
--   and this difference is negative if and only if
--   $$\frac{E_l}{E_s}>R=\frac{(1-n_H\lambda_H)\mu}{(m_H-\mu)(n_H\lambda_H-n'_H\lambda'_H)}.$$
--
--   This is the comparison behind part 1(a) and 2(a) of Proposition 3: MC raises sales (it covers the gaps) but lowers overproduction.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. a7 (PDF 39), proof of Proposition 3, case 1)

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

theorem impact_Hup_vs_Hu (P : Params) (hP : P.Standing) :
    impactHyb P (Hup P) - impactMP P (Hu P) =
        P.Es * P.μ * (1 - nH P * lamH P) -
          P.El * (P.mH - P.μ) * (nH P * lamH P - nHp P * lamHp P) ∧
      (impactHyb P (Hup P) < impactMP P (Hu P) ↔ R P < P.El / P.Es) := by sorry

end MCSustain.WinWin
