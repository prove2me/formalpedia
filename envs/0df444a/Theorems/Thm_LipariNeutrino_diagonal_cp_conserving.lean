-- Prove2me | Theorems.Thm_LipariNeutrino_diagonal_cp_conserving
-- name    : LipariNeutrino.diagonal_cp_conserving
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T12:05:43.562787+00:00
-- url     : https://prove2.me/theorems/2240fa5c-1196-477e-99cb-aa0c28df17e9
-- title:
--   No CP violation in survival probabilities
-- statement:
--   Let $U$ be any complex $n\times n$ matrix, $m_j^2$ real squared masses, $L$ a path length and $E$ an energy, with $P(\nu_\alpha\to\nu_\beta)=\bigl|\sum_j U_{\beta j}U^*_{\alpha j}e^{-im_j^2L/(2E)}\bigr|^2$ and $P(\bar\nu_\alpha\to\bar\nu_\beta)$ the same expression with $U$ replaced by $U^*$. Then for every flavour $\alpha$,
--
--   $$P(\bar\nu_\alpha\to\bar\nu_\alpha)=P(\nu_\alpha\to\nu_\alpha).$$
--
--   **Formalization Note** Unitarity of $U$ is not needed and not assumed.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.3, p. 135, fourth bullet after Eq. (62).

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

namespace LipariNeutrino

theorem diagonal_cp_conserving {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (m2 : Fin n → ℝ)
    (L E : ℝ) (α : Fin n) :
    oscProbBar U m2 L E α α = oscProb U m2 L E α α := by sorry

end LipariNeutrino
