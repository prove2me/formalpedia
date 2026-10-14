-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_potential_minimum
-- name    : MDOUnifiedCosmology.potential_minimum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:32:16.662752+00:00
-- url     : https://prove2.me/theorems/d304fe5f-1adc-4cb0-882d-d3078dd7810b
-- title:
--   The potential attains its minimum at $\phi_{\min}$, Eq. (21)
-- statement:
--   Let $V=V_1+V_2$ be the potential of Eq. (19), with $A>0$, $\phi_c>0$, and suppose the effective self-coupling is positive, $\tilde\alpha=\alpha+4A^4/\phi_c^4>0$ (equivalently $\alpha>-4A^4/\phi_c^4$). Define
--
--   $$\phi_{\min}=\phi_c\sqrt{\frac{1-m^2\phi_c^2/4A^4}{1+\alpha\phi_c^4/4A^4}}.$$
--
--   Then $V(\phi_{\min})\le V(\phi)$ for every real $\phi$, i.e. the minimum of the potential occurs at $\phi_{\min}$ (Eq. (21)).
--
--   **Formalization Note** Lean's real square root returns $0$ for negative arguments. When $m^2\ge4A^4/\phi_c^2$ the radicand is negative, $\phi_{\min}=0$, and the statement says that the minimum is at the origin, which is correct in that regime. In the regime the paper has in mind ($m^2\ll4A^4/\phi_c^2$) the radicand is positive and $\phi_{\min}\approx\phi_c$.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 4, Eqs. (20)–(21) and the sentence preceding (21)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem potential_minimum (A φc m α : ℝ) (hA : 0 < A) (hφc : 0 < φc)
    (hα : 0 < effCoupling A φc α) :
    ∀ φ : ℝ, potential A φc m α (phiMin A φc m α) ≤ potential A φc m α φ := by
  sorry

end MDOUnifiedCosmology
