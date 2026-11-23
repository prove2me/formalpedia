-- Prove2me | Theorems.Thm_GrothendieckLB_cubic_positivePart_gaussian_bound
-- name    : GrothendieckLB.cubic_positivePart_gaussian_bound
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T15:45:57.596846+00:00
-- url     : https://prove2.me/theorems/e0480d94-106f-4674-a604-c510b144d163
-- title:
--   Gaussian positive-part bound for priced Hermite cubics
-- statement:
--   Let $Z$ be a standard real Gaussian, let $\nu=\sqrt{2/\pi}$, and set $R=3\nu/2$. For $a\in\mathbb R^4$ write $p_a=\sum_{j=0}^3 a_j\psi_j$ in the orthonormal Gaussian Hermite basis. For any real price $c$, prove
--   $$
--   \mathbb E\big[(|p_a(Z)|-c|Z|)_+\big]\ \le\ R\big(\sqrt{\|a\|_2^2+c^2}-c\big).
--   $$
--
--   This is the support-function form of the fiber inequality. The left side is an explicit one-dimensional integral depending on five real parameters. At each $z$ its integrand is the maximum of $v p_a(z)-c|z|v^2$ over $v\in\{-1,0,1\}$. The right side is the support function of the ball of radius $R$ centered at $(0,R)$ in Hermite-moment and budget coordinates, evaluated in direction $(a,-c)$.
--
--   The displayed form is obtained by homogeneity and pointwise maximization. In the source, Lemma D.2 and equation (56) use unit cubics and certify the priced bound for $c\ge 0.993405$. The large-budget estimate of Lemma D.1 and the overlap in Proposition D.3 cover the rest of the moment ball. The converse implication back to arbitrary ternary functions follows by testing the direction determined by their four Hermite moments and their budget.
-- source:
--   R. Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, https://arxiv.org/pdf/2608.11158v2, Appendix D.1, Lemma D.2 and the remark on exactness of the threshold reduction, pp. 49–50. Homogeneous support-function form of the fiber inequality, derived from the pointwise duality in the remark.

import Definitions.Def_GrothendieckLB_stdExp
import Definitions.Def_GrothendieckLB_he
import Definitions.Def_ABPOnline_cG

namespace GrothendieckLB

theorem cubic_positivePart_gaussian_bound (a : Fin 4 → ℝ) (c : ℝ) :
    stdExp (fun z => max 0 (|∑ j, a j * he j z| - c * |z|)) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt ((∑ j, a j ^ 2) + c ^ 2) - c) := by sorry

end GrothendieckLB
