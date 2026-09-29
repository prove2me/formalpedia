-- Prove2me | Theorems.Thm_GrandUnifiedTheories_beta_eq_one_iff
-- name    : GrandUnifiedTheories.beta_eq_one_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:56:44.499949+00:00
-- url     : https://prove2.me/theorems/ed4dc154-f8f4-4283-8c5b-55a0f080d774
-- title:
--   The kernel of $\beta$, explicitly
-- statement:
--   An element $x = (\alpha, g, h)$ of $G_{\mathrm{SM}}$ lies in the kernel of the Pati-Salam map $\beta$ if and only if
--
--   $$\alpha^{3} = 1,\qquad g = I_2,\qquad h = \alpha^{-1}I_3 .$$
--
--   So the kernel consists of the three elements $(\alpha, I, \alpha^{-1}I)$ with $\alpha$ a cube root of unity. Note the contrast with the $\mathrm{SU}(5)$ side: the weak-isospin factor $\mathrm{SU}(2)$ appears untouched in $\beta$, so no element with $g\ne I$ can be killed, and the kernel is a $\mathbb{Z}_3$ rather than a $\mathbb{Z}_6$. The remaining factor of two appears only after passing from $\mathrm{SO}(4)\times\mathrm{SO}(6)$ to its double cover, which is where the $\mathbb{Z}_6$ of Theorem 9 comes from.
--
--   **Formalization note.** The source states the map $\beta$ and uses it, but does not display this kernel computation; the statement is the direct elementwise computation for the $\beta$ of p. 54.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 3.3, p. 54 (kernel of the displayed map β; the computation is elementary from the formula for β and is not displayed in the source)

import Mathlib
import Definitions.Def_GUT_standard_model_group

namespace GrandUnifiedTheories

theorem beta_eq_one_iff (x : GSM) :
    betaMatrix x = (1, 1, 1) ↔
      ((x.1 : ℂ) ^ 3 = 1 ∧
        (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
        (x.2.2 : Matrix (Fin 3) (Fin 3) ℂ) = (((x.1)⁻¹ : Circle) : ℂ) • 1) := by sorry

end GrandUnifiedTheories
