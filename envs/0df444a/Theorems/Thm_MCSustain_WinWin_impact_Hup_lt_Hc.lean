-- Prove2me | Theorems.Thm_MCSustain_WinWin_impact_Hup_lt_Hc
-- name    : MCSustain.WinWin.impact_Hup_lt_Hc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:25.676011+00:00
-- url     : https://prove2.me/theorems/ec3d49c7-eedd-4549-8bfe-45b78f342283
-- title:
--   Proof of Proposition 3, p. a7 (PDF 39), case 2) — for f'_H < f ≤ f_H, ℍ'_u has lower expected impact than ℍ_c
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   If $f'_H<f\le f_H$, the hybrid solution $\mathbb H'_u$ has strictly lower expected environmental impact than the MP solution $\mathbb H_c$:
--   $$\mathbb E[I_{\mathbb H'_u}]<\mathbb E[I_{\mathbb H_c}].$$
--
--   This is the comparison behind parts 1(b), 2(b) and 3 of Proposition 3.
--
--   **Formalization Note** The strict inequality uses $E_l>0$, one of the added standing assumptions.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. a7 (PDF 39), proof of Proposition 3, case 2)

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

theorem impact_Hup_lt_Hc (P : Params) (hP : P.Standing) (hf1 : fHp P < P.f)
    (hf2 : P.f ≤ fH P) :
    impactHyb P (Hup P) < impactMP P (Hc P) := by sorry

end MCSustain.WinWin
