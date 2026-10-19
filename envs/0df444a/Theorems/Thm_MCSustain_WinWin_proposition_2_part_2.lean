-- Prove2me | Theorems.Thm_MCSustain_WinWin_proposition_2_part_2
-- name    : MCSustain.WinWin.proposition_2_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:29.137287+00:00
-- url     : https://prove2.me/theorems/1e5de291-d846-4b04-9775-07f6ca3fb712
-- title:
--   Proposition 2, part 2, p. 16 (PDF 16) — hybrid solution for a moderate-value product, by w and f
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   Suppose $\kappa_1\le r/c<\kappa_2$. Then the following decisions are optimal for the hybrid firm:
--   1. $\mathbb L'_u$ when $w>w_1$ and $f>f'_L$;
--   2. $\mathbb L'_c$ when $w>w_1$ and $f'_L\ge f\ge f'_{cu}$;
--   3. $\mathbb H'_u$ when $w\le w_1$ and $f>f'_H$, or $w>w_1$ and $f'_{cu}>f>f'_H$;
--   4. $\mathbb H'_c$ when $f\le f'_H$.
--
--   **Formalization Note** Uniqueness is not claimed (at $f=f'_{cu}$ two types tie).
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. 16 (PDF 16), Proposition 2, part 2 (preamble p. 15)

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

theorem proposition_2_part_2 (P : Params) (hP : P.Standing) (hκ1 : κ1 P ≤ P.r / P.c)
    (hκ2 : P.r / P.c < κ2 P) :
    (w1 P < P.w ∧ fLp P < P.f → IsOptHyb P (Lup P)) ∧
      (w1 P < P.w ∧ P.f ≤ fLp P ∧ fcup P ≤ P.f → IsOptHyb P (Lcp P)) ∧
      ((P.w ≤ w1 P ∧ fHp P < P.f) ∨ (w1 P < P.w ∧ P.f < fcup P ∧ fHp P < P.f) →
        IsOptHyb P (Hup P)) ∧
      (P.f ≤ fHp P → IsOptHyb P (Hcp P)) := by sorry

end MCSustain.WinWin
