-- Prove2me | Theorems.Thm_MCSustain_WinWin_proposition_1_part_2
-- name    : MCSustain.WinWin.proposition_1_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:16.052554+00:00
-- url     : https://prove2.me/theorems/c7edbe3e-e981-439a-8e55-d664d444a36b
-- title:
--   Proposition 1, part 2, p. 11 (PDF 11) — MP solution for a moderate-value product: 𝕃_u, 𝕃_c, ℍ_u or ℍ_c by f
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   Suppose the product is of moderate value, $\kappa_1\le r/c<\kappa_2$. Then the following decisions are optimal for the MP firm:
--   1. $\mathbb L_u$ when $f>f_L$;
--   2. $\mathbb L_c$ when $f_L\ge f\ge f_{cu}$;
--   3. $\mathbb H_u$ when $f_{cu}>f>f_H$;
--   4. $\mathbb H_c$ when $f\le f_H$.
--
--   **Formalization Note** Uniqueness is not claimed: at $f=f_{cu}$ both $\mathbb L_c$ and $\mathbb H_u$ are optimal.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. 11 (PDF 11), Proposition 1, part 2

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

theorem proposition_1_part_2 (P : Params) (hP : P.Standing) (hκ1 : κ1 P ≤ P.r / P.c)
    (hκ2 : P.r / P.c < κ2 P) :
    (fL P < P.f → IsOptMP P (Lu P)) ∧
      (P.f ≤ fL P ∧ fcu P ≤ P.f → IsOptMP P (Lc P)) ∧
      (P.f < fcu P ∧ fH P < P.f → IsOptMP P (Hu P)) ∧
      (P.f ≤ fH P → IsOptMP P (Hc P)) := by sorry

end MCSustain.WinWin
