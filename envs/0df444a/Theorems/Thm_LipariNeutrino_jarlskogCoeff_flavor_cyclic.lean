-- Prove2me | Theorems.Thm_LipariNeutrino_jarlskogCoeff_flavor_cyclic
-- name    : LipariNeutrino.jarlskogCoeff_flavor_cyclic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T11:28:50.41411+00:00
-- url     : https://prove2.me/theorems/02221d20-cc35-489d-94ca-1370880d5102
-- title:
--   $J^{e\mu}_{jk}=J^{\mu\tau}_{jk}=J^{\tau e}_{jk}$ for unitary $3\times3$ mixing
-- statement:
--   Let $U$ be a unitary complex $3\times3$ matrix with rows indexed by the flavours $e,\mu,\tau$, and let $J^{\alpha\beta}_{jk}=-\mathrm{Im}[U_{\alpha j}U^*_{\alpha k}U^*_{\beta j}U_{\beta k}]$. Then for all mass indices $j,k$,
--
--   $$J^{e\mu}_{jk}=J^{\mu\tau}_{jk}=J^{\tau e}_{jk}.$$
--
--   **Formalization Note** Flavours $e,\mu,\tau$ are the row indices $0,1,2$.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.3, p. 136, Eq. (68) and footnote 8.

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

namespace LipariNeutrino

theorem jarlskogCoeff_flavor_cyclic (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) (j k : Fin 3) :
    jarlskogCoeff U 0 1 j k = jarlskogCoeff U 1 2 j k ∧
    jarlskogCoeff U 1 2 j k = jarlskogCoeff U 2 0 j k := by sorry

end LipariNeutrino
