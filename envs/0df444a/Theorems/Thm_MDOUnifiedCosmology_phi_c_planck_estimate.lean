-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_phi_c_planck_estimate
-- name    : MDOUnifiedCosmology.phi_c_planck_estimate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:35:17.542978+00:00
-- url     : https://prove2.me/theorems/2fa6db9e-50e2-4e6a-bd99-8eb53187b7d4
-- title:
--   Planck values give $\phi_c \simeq 1.3\, m_{pl}$
-- statement:
--   With the Planck values $\Omega_b=0.05$ and $\Omega_{DM,\phi}=0.27$, the formula $\phi_c=m_{pl}\sqrt{\Omega_{DM,\phi}/(\pi\Omega_b)}$ gives $\phi_c\simeq1.3\,m_{pl}$; precisely,
--
--   $$1.3<\sqrt{\frac{0.27}{0.05\,\pi}}<1.32.$$
--
--   This is the numerical estimate stated before Eq. (27).
--
--   **Formalization Note** The paper's "$\simeq 1.3$" is encoded as the explicit enclosure $(1.3, 1.32)$.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 5, Sect. 3, sentence before Eq. (27): $\Omega_b \simeq 0.05$, $\Omega_{DM,\phi}\simeq 0.27$ give $\phi_c\simeq 1.3\,m_{pl}$

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem phi_c_planck_estimate :
    1.3 < Real.sqrt (0.27 / (Real.pi * 0.05)) ∧ Real.sqrt (0.27 / (Real.pi * 0.05)) < 1.32 := by
  sorry

end MDOUnifiedCosmology
