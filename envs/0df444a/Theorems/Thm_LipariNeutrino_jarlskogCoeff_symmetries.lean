-- Prove2me | Theorems.Thm_LipariNeutrino_jarlskogCoeff_symmetries
-- name    : LipariNeutrino.jarlskogCoeff_symmetries
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T05:06:37.329991+00:00
-- url     : https://prove2.me/theorems/6133083a-17cc-4859-9e7e-76aca396a0e8
-- title:
--   Symmetries of the coefficients $J^{\alpha\beta}_{jk}$
-- statement:
--   Let $U$ be any complex $n\times n$ matrix and define
--
--   $$J^{\alpha\beta}_{jk}=-\mathrm{Im}\bigl[U_{\alpha j}U^*_{\alpha k}U^*_{\beta j}U_{\beta k}\bigr].$$
--
--   Then for all indices $\alpha,\beta,j,k$:
--
--   1. $J^{\alpha\beta}_{jk}=-J^{\alpha\beta}_{kj}$;
--   2. $J^{\alpha\beta}_{jk}=-J^{\beta\alpha}_{jk}$;
--   3. $J^{\alpha\beta}_{jj}=0$;
--   4. $J^{\alpha\alpha}_{jk}=0$.
--
--   These are the elementary symmetry properties of the CP/T-odd coefficients of the oscillation probability.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.3, p. 136, Eqs. (65)-(66).

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

namespace LipariNeutrino

theorem jarlskogCoeff_symmetries {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (α β j k : Fin n) :
    jarlskogCoeff U α β j k = -jarlskogCoeff U α β k j ∧
    jarlskogCoeff U α β j k = -jarlskogCoeff U β α j k ∧
    jarlskogCoeff U α β j j = 0 ∧
    jarlskogCoeff U α α j k = 0 := by sorry

end LipariNeutrino
