-- Prove2me | Theorems.Thm_LipariNeutrino_jarlskogCoeff_mass_cyclic
-- name    : LipariNeutrino.jarlskogCoeff_mass_cyclic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T05:10:26.862111+00:00
-- url     : https://prove2.me/theorems/bebb0a2d-e04f-475d-835b-f15666489eca
-- title:
--   $J^{\alpha\beta}_{12}=J^{\alpha\beta}_{23}=J^{\alpha\beta}_{31}$ for unitary $3\times3$ mixing
-- statement:
--   Let $U$ be a unitary complex $3\times3$ matrix ($UU^\dagger=U^\dagger U=I$) and let $J^{\alpha\beta}_{jk}=-\mathrm{Im}[U_{\alpha j}U^*_{\alpha k}U^*_{\beta j}U_{\beta k}]$. Then for all flavour indices $\alpha,\beta$,
--
--   $$J^{\alpha\beta}_{12}=J^{\alpha\beta}_{23}=J^{\alpha\beta}_{31}.$$
--
--   Together with Eq. (68) this shows that a single real number, the Jarlskog parameter, controls all CP/T-odd effects in three-flavour vacuum oscillations.
--
--   **Formalization Note** Mass indices $1,2,3$ are $0,1,2$ in Lean.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.3, p. 136, Eq. (67) and footnote 8.

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

namespace LipariNeutrino

theorem jarlskogCoeff_mass_cyclic (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) (α β : Fin 3) :
    jarlskogCoeff U α β 0 1 = jarlskogCoeff U α β 1 2 ∧
    jarlskogCoeff U α β 1 2 = jarlskogCoeff U α β 2 0 := by sorry

end LipariNeutrino
