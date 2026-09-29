-- Prove2me | Theorems.Thm_LipariNeutrino_cpt_invariance
-- name    : LipariNeutrino.cpt_invariance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T12:03:39.289316+00:00
-- url     : https://prove2.me/theorems/50e2fae1-4a37-44f7-b6ae-3aba271e9e7d
-- title:
--   CPT invariance of vacuum oscillations: $P(\nu_\alpha\to\nu_\beta)=P(\bar\nu_\beta\to\bar\nu_\alpha)$
-- statement:
--   Let $U$ be any complex $n\times n$ matrix, $m_j^2$ real squared masses, $L$ a path length and $E$ an energy. Define $P(\nu_\alpha\to\nu_\beta)=\bigl|\sum_j U_{\beta j}U^*_{\alpha j}e^{-im_j^2L/(2E)}\bigr|^2$ and let $P(\bar\nu_\alpha\to\bar\nu_\beta)$ be the same expression with $U$ replaced by its entrywise complex conjugate $U^*$. Then for all $\alpha,\beta$,
--
--   $$P(\nu_\alpha\to\nu_\beta)=P(\bar\nu_\beta\to\bar\nu_\alpha).$$
--
--   **Formalization Note** Unitarity of $U$ is not needed and not assumed.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.3, pp. 134-135, Eq. (60) and the third bullet after Eq. (62).

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

namespace LipariNeutrino

theorem cpt_invariance {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (m2 : Fin n → ℝ) (L E : ℝ)
    (α β : Fin n) :
    oscProb U m2 L E α β = oscProbBar U m2 L E β α := by sorry

end LipariNeutrino
