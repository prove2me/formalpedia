-- Prove2me | Theorems.Thm_MCSustain_WinWin_fcup_spec
-- name    : MCSustain.WinWin.fcup_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:14.976476+00:00
-- url     : https://prove2.me/theorems/206bcfee-121d-4491-9d93-0fa265f694ba
-- title:
--   Table 2, p. a1 (PDF 33) — where Proposition 2 uses it, f'_cu is the unique root on (f'_H, f'_L]
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   Suppose either the product is of moderate value ($\kappa_1\le r/c<\kappa_2$) and $w>w_1$, or it is of low value ($r/c<\kappa_1$) and $w_1<w<w_2$. Let
--   $$\Phi'(g)=\lambda'_L-\tfrac32\Big(\frac{g}{2m_Lt}\Big)^{1/3}-\frac{\lambda_H'^4\mu\beta t}{16g}.$$
--   Then
--   $$f'_H<f'_{cu}<f'_L,\qquad \Phi'(f'_{cu})=0,\qquad \Phi'(g)=0,\ f'_H<g\le f'_L\ \Rightarrow\ g=f'_{cu}.$$
--
--   These are exactly the cases of Proposition 2 that use $f'_{cu}$.
--
--   **Formalization Note** Uniqueness is stated on $(f'_H,f'_L]$, and `fcup` is the infimum of the roots there.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. a1 (PDF 33), Table 2 (row f′_cu)

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

theorem fcup_spec (P : Params) (hP : P.Standing)
    (hreg : (κ1 P ≤ P.r / P.c ∧ P.r / P.c < κ2 P ∧ w1 P < P.w) ∨
      (P.r / P.c < κ1 P ∧ w1 P < P.w ∧ P.w < w2 P)) :
    fHp P < fcup P ∧ fcup P < fLp P ∧ Φp P (fcup P) = 0 ∧
      ∀ g : ℝ, fHp P < g → g ≤ fLp P → Φp P g = 0 → g = fcup P := by sorry

end MCSustain.WinWin
