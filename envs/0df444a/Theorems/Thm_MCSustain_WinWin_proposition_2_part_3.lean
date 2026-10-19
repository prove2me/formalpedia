-- Prove2me | Theorems.Thm_MCSustain_WinWin_proposition_2_part_3
-- name    : MCSustain.WinWin.proposition_2_part_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:40.472978+00:00
-- url     : https://prove2.me/theorems/a9c6f086-169b-4168-bd1d-b375cfe67f08
-- title:
--   Proposition 2, part 3, p. 16 (PDF 16) — hybrid solution for a low-value product, by w and f
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   Suppose $r/c<\kappa_1$. Then the following decisions are optimal for the hybrid firm:
--   1. $\mathbb L'_u$ when $w>w_1$ and $f>f'_L$;
--   2. $\mathbb L'_c$ when $w_1<w<w_2$ and $f'_L\ge f\ge f'_{cu}$, or $w\ge w_2$ and $f'_L\ge f\ge f_c$;
--   3. $\mathbb H'_u$ when $w\le w_1$ and $f>f'_H$, or $w_1<w<w_2$ and $f'_{cu}>f>f'_H$;
--   4. $\mathbb H'_c$ when $w<w_2$ and $f\le f'_H$, or $w\ge w_2$ and $f\le f_c$.
--
--   **Formalization Note** Uniqueness is not claimed: cases 2 and 4 overlap at $w\ge w_2$, $f=f_c$, where both types are optimal; the printed bounds are kept.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. 16 (PDF 16), Proposition 2, part 3 (preamble p. 15)

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

theorem proposition_2_part_3 (P : Params) (hP : P.Standing) (hv : P.r / P.c < κ1 P) :
    (w1 P < P.w ∧ fLp P < P.f → IsOptHyb P (Lup P)) ∧
      ((w1 P < P.w ∧ P.w < w2 P ∧ P.f ≤ fLp P ∧ fcup P ≤ P.f) ∨
          (w2 P ≤ P.w ∧ P.f ≤ fLp P ∧ fc P ≤ P.f) → IsOptHyb P (Lcp P)) ∧
      ((P.w ≤ w1 P ∧ fHp P < P.f) ∨ (w1 P < P.w ∧ P.w < w2 P ∧ P.f < fcup P ∧ fHp P < P.f) →
        IsOptHyb P (Hup P)) ∧
      ((P.w < w2 P ∧ P.f ≤ fHp P) ∨ (w2 P ≤ P.w ∧ P.f ≤ fc P) → IsOptHyb P (Hcp P)) := by sorry

end MCSustain.WinWin
