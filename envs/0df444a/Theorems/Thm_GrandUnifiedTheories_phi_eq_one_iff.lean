-- Prove2me | Theorems.Thm_GrandUnifiedTheories_phi_eq_one_iff
-- name    : GrandUnifiedTheories.phi_eq_one_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:42:23.362786+00:00
-- url     : https://prove2.me/theorems/20b4fef0-ec27-4628-979a-1aad9cd65b3f
-- title:
--   The kernel of $\varphi$, explicitly
-- statement:
--   An element $x = (\alpha, g, h)$ of $G_{\mathrm{SM}}$ lies in the kernel of $\varphi$ if and only if
--
--   $$\alpha^{6} = 1,\qquad g = \alpha^{-3} I_2, \qquad h = \alpha^{2} I_3 .$$
--
--   In words: the kernel consists exactly of the elements $(\alpha, \alpha^{-3}I, \alpha^{2}I)$ with $\alpha$ a sixth root of unity. The scalar matrices $\alpha^{-3}I_2$ and $\alpha^{2}I_3$ have determinants $\alpha^{-6}$ and $\alpha^{6}$, so they lie in $\mathrm{SU}(2)$ and $\mathrm{SU}(3)$ precisely when $\alpha^{6} = 1$; that is the source of the condition $\alpha^6 = 1$, which is therefore implied by the other two.
--
--   This is the computation behind the statement that the $\mathrm{SU}(5)$ theory does not see all of $G_{\mathrm{SM}}$, only the quotient $G_{\mathrm{SM}}/\mathbb{Z}_6$: any representation pulled back from $\mathrm{SU}(5)$ must act trivially on these six elements.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 3.1, p. 34 ('the map φ has a kernel, Z₆. The kernel is the set of all elements of the form (α, α⁻³, α²)')

import Mathlib
import Definitions.Def_GUT_standard_model_group

namespace GrandUnifiedTheories

theorem phi_eq_one_iff (x : GSM) :
    phiMatrix x = 1 ↔
      ((x.1 : ℂ) ^ 6 = 1 ∧
        (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = (((x.1)⁻¹ : Circle) : ℂ) ^ 3 • 1 ∧
        (x.2.2 : Matrix (Fin 3) (Fin 3) ℂ) = ((x.1 : ℂ) ^ 2) • 1) := by sorry

end GrandUnifiedTheories
