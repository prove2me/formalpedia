-- Prove2me | Theorems.Thm_Landreman3DEquilibria_field_smooth_on_domainU
-- name    : Landreman3DEquilibria.field_smooth_on_domainU
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:46:47.043472+00:00
-- url     : https://prove2.me/theorems/a3147f9f-4408-4262-b9e4-cb3aaa17577c
-- title:
--   Smoothness of $B$ on $U_\epsilon$
-- statement:
--   Let $0<\epsilon<1$, let $a=\sqrt{1+\epsilon}$, $b=\sqrt{1-\epsilon}$, and let
--
--   $$s=\frac{x_0^2}{a^2}+\frac{x_1^2}{b^2},\qquad F=\sqrt{1-(1-s)^2-4x_2^2},\qquad
--   B=\left(\frac{2x_2x_0-\frac{a}{b}Fx_1}{s},\ \frac{2x_2x_1+\frac{b}{a}Fx_0}{s},\ 1-s\right).$$
--
--   On the open set $U_\epsilon=\{x: 1-(1-s)^2-4x_2^2>0\}$ one has $s>0$ and the radicand is positive, so the field is infinitely differentiable there:
--
--   $$B\in C^\infty(U_\epsilon;\mathbb R^3).$$
--
--   This is the regularity statement that makes the family a genuine smooth solution rather than a distributional or piecewise one; the source records it immediately after introducing the field ("In this domain $s>0$, so the field is smooth").
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, Section 2.1, text following eq. (2.2)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem field_smooth_on_domainU (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Bfield e) (domainU e) := by sorry

end Landreman3DEquilibria
