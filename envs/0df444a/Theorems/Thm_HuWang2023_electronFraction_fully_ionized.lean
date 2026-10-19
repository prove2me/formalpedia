-- Prove2me | Theorems.Thm_HuWang2023_electronFraction_fully_ionized
-- name    : HuWang2023.electronFraction_fully_ionized
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:43:26.773973+00:00
-- url     : https://prove2.me/theorems/2c2add17-1350-435d-b9bb-aa5a55834ffa
-- title:
--   Electron fraction of a fully ionized IGM: $f_e = 7/8$
-- statement:
--   With hydrogen fraction $Y_H = 0.75$, helium fraction $Y_{He} = 0.25$ and complete ionization $X_{e,H} = X_{e,He} = 1$ (valid at $z<3$), the electron fraction $f_e = Y_HX_{e,H} + \tfrac12 Y_{He}X_{e,He}$ appearing in Eq. (5) equals
--   $$f_e = \frac78.$$
--
--   This is the value of $f_e$ that enters the FRB dispersion measure in the redshift range used in Section 3.4.
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 3.4, p. 6, text following Eq. (5)

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs

namespace HuWang2023

theorem electronFraction_fully_ionized :
    electronFraction 0.75 1 0.25 1 = 7 / 8 := by sorry

end HuWang2023
