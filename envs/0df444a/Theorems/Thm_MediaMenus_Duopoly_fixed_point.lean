-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_fixed_point
-- name    : MediaMenus.Duopoly.fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:55.688607+00:00
-- url     : https://prove2.me/theorems/22ac7768-450b-4bc0-9e45-165a77f4e928
-- title:
--   Proof of Proposition 3, pp. 58–59 — the best-response equations (22) have the unique fixed point a^L = (w−d^L)/3, a^H = α/3
-- statement:
--   Let $a^L_1,a^H_1,a^L_2,a^H_2$ be real numbers such that, for $(i,j)=(1,2)$ and $(i,j)=(2,1)$, the best-response equations (22) hold:
--   $$a^L_i=\Big(\max\Big(\tfrac{w-d^L-a^L_j}{2},\ \tfrac{w-d^H-(r^La^L_j+r^Ha^H_j)}{2}\Big)\Big)^+,\qquad a^H_i=\Big(\min\Big(\tfrac{r^H(w-d^H-a^H_j)-r^L(d^H-d^L)}{2r^H},\ \tfrac{w-d^H-(r^La^L_j+r^Ha^H_j)}{2}\Big)\Big)^+,$$
--   with $r^L=1-r$, $r^H=r$. Then, under the standing assumptions,
--   $$a^L_1=a^L_2=\frac{w-d^L}{3},\qquad a^H_1=a^H_2=\frac{\alpha}{3}.$$
--
--   This is the algebraic core of the uniqueness part of Proposition 3.
--
--   **Formalization Note.** The paper writes the second conclusion as $a^H_1=a^H_2=(r^H(w-d^H)-r^L(d^H-d^L))^+/(3r^H)$, which equals $\alpha/3$ because $r^H=r>0$. Page 59 prints "$a^L_1=a^2_L$"; this is read as $a^L_1=a^L_2$.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), pp. 58–59, proof of Proposition 3, fixed point of (22)

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem fixed_point (P : Params) (hS : P.Standing) (aL aH : Fin 2 → ℝ)
    (hL : ∀ i, aL i = brAdL P (aL (other i)) (aH (other i)))
    (hH : ∀ i, aH i = brAdH P (aL (other i)) (aH (other i))) :
    ∀ i, aL i = (P.w - P.dL) / 3 ∧ aH i = alphaQ P / 3 := by sorry

end MediaMenus.Duopoly
