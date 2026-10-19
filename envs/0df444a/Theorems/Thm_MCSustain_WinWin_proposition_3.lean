-- Prove2me | Theorems.Thm_MCSustain_WinWin_proposition_3
-- name    : MCSustain.WinWin.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:49.645033+00:00
-- url     : https://prove2.me/theorems/e7fd70b5-1105-40d0-a557-d990cc3814a7
-- title:
--   Proposition 3, p. 18 (PDF 18) — exactly when adopting mass customization is a win-win for profit and environmental impact
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   Adopting MC is a **win-win** when both the MP and the hybrid problem have optimal decisions and every optimal hybrid decision has strictly higher expected profit and strictly lower expected environmental impact than every optimal MP decision. For every parameter point satisfying the standing assumptions, adopting MC is a win-win if and only if one of the following holds:
--   1. the product has high value, $r/c\ge\kappa_2$, and
--      (a) $f>f_H$ and $E_l/E_s>R$, or (b) $f_H\ge f>f'_H$;
--   2. the product has moderate value, $\kappa_1\le r/c<\kappa_2$, and
--      (a) $f_{cu}>f>f_H$ and $E_l/E_s>R$, or (b) $f_H\ge f>f'_H$;
--   3. the product has low value, $r/c<\kappa_1$, and $f_c>f>f'_H$ and $w\le w_2$.
--
--   In symbols,
--   $$\mathrm{WinWin}\iff \mathrm{(1)}\ \lor\ \mathrm{(2)}\ \lor\ \mathrm{(3)}.$$
--
--   The result shows that MC is not automatically greener: when it pushes the MP line towards stocking for the high market size, it increases overproduction, and the net effect depends on the leftover-to-sold impact ratio $E_l/E_s$.
--
--   **Formalization Note** "Fully characterize" is read as an equivalence over the whole parameter space. Part 2(a) prints the condition "$E_l/E_s>R$" twice; it is stated once. The win-win is stated in terms of all optimal decisions, not the solution types, so the strict boundaries of the printed regions ($f<f_{cu}$, $f<f_c$, $f>f'_H$) are where ties between optima occur. $E_l>0$ is added to the standing assumptions: with $E_l=0$ the impacts in case 1(b) tie.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. 18 (PDF 18), Proposition 3

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

/-- Proposition 3 (p. 18). Part 2(a) prints the condition "E_l/E_s > R" twice; it is stated
once here. -/
theorem proposition_3 (P : Params) (hP : P.Standing) :
    WinWin P ↔
      (κ2 P ≤ P.r / P.c ∧
          ((fH P < P.f ∧ R P < P.El / P.Es) ∨ (P.f ≤ fH P ∧ fHp P < P.f))) ∨
      (κ1 P ≤ P.r / P.c ∧ P.r / P.c < κ2 P ∧
          ((P.f < fcu P ∧ fH P < P.f ∧ R P < P.El / P.Es) ∨ (P.f ≤ fH P ∧ fHp P < P.f))) ∨
      (P.r / P.c < κ1 P ∧ P.f < fc P ∧ fHp P < P.f ∧ P.w ≤ w2 P) := by sorry

end MCSustain.WinWin
