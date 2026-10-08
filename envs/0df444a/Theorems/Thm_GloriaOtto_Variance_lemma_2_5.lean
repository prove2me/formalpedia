-- Prove2me | Theorems.Thm_GloriaOtto_Variance_lemma_2_5
-- name    : GloriaOtto.Variance.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:11.544811+00:00
-- url     : https://prove2.me/theorems/0065ceba-9aea-47dd-a6c4-314e464ccb03
-- title:
--   Lemma 2.5 — ∂G_T(x,y)/∂a(e) = −∇_{z_i}G_T(x,z)∇_{z_i}G_T(z,y), and sup_{a(e)} |∇_{z_i}G_T(z,x)| ≲ |∇_{z_i}G_T(z,x)|
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$, $a \in \mathcal A_{\alpha\beta}$, $T > 0$, and let $e = [z, z+e_i]$ be an edge.
--
--   1. (2.15) For all $x, y \in \mathbb Z^d$, the map $t \mapsto G_T(x,y; a^{e\to t})$, where $a^{e\to t}$ is $a$ with the value on $e$ replaced by $t$, is differentiable at $t = a(e)$ with
--   $$\frac{\partial}{\partial a(e)}G_T(x,y;a) = -\big(G_T(x,z+e_i;a) - G_T(x,z;a)\big)\big(G_T(z+e_i,y;a) - G_T(z,y;a)\big),$$
--   i.e. $-\nabla_{z_i}G_T(x,z;a)\,\nabla_{z_i}G_T(z,y;a)$.
--   2. (2.16) There is a constant $C$ depending only on $d, \alpha, \beta$ such that for all such $a, T, e$, all $x$ and every value $t \in [\alpha,\beta]$ of $a(e)$,
--   $$|\nabla_{z_i}G_T(z,x;a^{e\to t})| \le C\,|\nabla_{z_i}G_T(z,x;a)| .$$
--
--   The formula expresses the sensitivity of the Green's function to one conductivity. The bound shows that changing one conductivity changes the gradient of $G_T$ across that edge by at most a bounded factor.
--
--   **Formalization Note.** In (2.15) the difference in $G_T(x,\cdot)$ is taken in the second argument and the difference in $G_T(\cdot,y)$ in the first, as printed. "$\sup_{a(e)}$" is rendered as "for every value $t \in [\alpha,\beta]$ of $a(e)$, the other conductivities fixed".
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Lemma 2.5, (2.15), (2.16), p. 17

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem lemma_2_5 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    (∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T →
      ∀ (z : Site d) (i : Fin d) (x y : Site d),
        HasDerivAt (fun t => greenT (Function.update a (z, i) t) T x y)
          (-(greenT a T x (z + unit i) - greenT a T x z)
            * (greenT a T (z + unit i) y - greenT a T z y))
          (a (z, i))) ∧
    (∃ C : ℝ, ∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T →
      ∀ (z : Site d) (i : Fin d) (x : Site d), ∀ t ∈ Set.Icc α β,
        |greenT (Function.update a (z, i) t) T (z + unit i) x
            - greenT (Function.update a (z, i) t) T z x|
          ≤ C * |greenT a T (z + unit i) x - greenT a T z x|) := by sorry

end GloriaOtto.Variance
