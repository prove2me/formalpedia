-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_potential_expanded_form
-- name    : MDOUnifiedCosmology.potential_expanded_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:31:38.620071+00:00
-- url     : https://prove2.me/theorems/d3077047-b0d5-4b43-be56-75145db7456f
-- title:
--   Expanded form of the potential with effective mass and coupling, Eq. (20)
-- statement:
--   Let $V(\phi)=V_1(\phi)+V_2(\phi)$ with $V_1(\phi)=A^4(1-\phi^2/\phi_c^2)^2$ (Eq. (17)) and $V_2(\phi)=\frac12m^2\phi^2+\frac\alpha4\phi^4$ (Eq. (18)), where $\phi_c\neq0$. Then for every real $\phi$
--
--   $$V(\phi)=\frac12 m_{\mathrm{eff}}^2\phi^2+\frac{\tilde\alpha}{4}\phi^4+A^4,$$
--
--   with effective mass $m_{\mathrm{eff}}^2=m^2-4A^4/\phi_c^2$ and effective self-coupling $\tilde\alpha=\alpha+4A^4/\phi_c^4$. This is Eq. (20), with constant $C=A^4$.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 4, Eqs. (17)–(20)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem potential_expanded_form (A φc m α : ℝ) (hφc : φc ≠ 0) (φ : ℝ) :
    potential A φc m α φ =
      1 / 2 * effMassSq A φc m * φ ^ 2 + effCoupling A φc α / 4 * φ ^ 4 + A ^ 4 := by
  sorry

end MDOUnifiedCosmology
