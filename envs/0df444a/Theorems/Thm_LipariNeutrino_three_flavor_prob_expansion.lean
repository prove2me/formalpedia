-- Prove2me | Theorems.Thm_LipariNeutrino_three_flavor_prob_expansion
-- name    : LipariNeutrino.three_flavor_prob_expansion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T05:03:17.479565+00:00
-- url     : https://prove2.me/theorems/78b53515-a8a6-43f1-98d9-250a1b4246c9
-- title:
--   Three-flavour oscillation probability: constant, cosine and sine terms
-- statement:
--   Let $U$ be any complex $3\times 3$ matrix (rows: flavours, columns: mass eigenstates), let $m_1^2,m_2^2,m_3^2$ be real numbers, $L$ a path length and $E$ an energy, and write $\Delta m^2_{jk}=m_k^2-m_j^2$. With
--
--   $$P(\nu_\alpha\to\nu_\beta)=\Bigl|\sum_{j=1}^3 U_{\beta j}U^*_{\alpha j}\,e^{-i m_j^2 L/(2E)}\Bigr|^2,$$
--
--   for all flavours $\alpha,\beta$,
--
--   $$P(\nu_\alpha\to\nu_\beta)=\sum_{j}|U_{\beta j}|^2|U_{\alpha j}|^2+\sum_{j<k}2\,\mathrm{Re}\bigl[U^*_{\beta j}U_{\beta k}U_{\alpha j}U^*_{\alpha k}\bigr]\cos\frac{\Delta m^2_{jk}L}{2E}+\sum_{j<k}2\,\mathrm{Im}\bigl[U^*_{\beta j}U_{\beta k}U_{\alpha j}U^*_{\alpha k}\bigr]\sin\frac{\Delta m^2_{jk}L}{2E}.$$
--
--   This decomposition separates the CP-even (cosine) part of the probability from the CP-odd (sine) part.
--
--   **Formalization Note** Unitarity of $U$ is not needed for this identity and is not assumed. The printed Eq. (61) has $|U_{\beta j}|^4|U_{\alpha j}|^4$ in the constant term; this is a misprint and the exponent $2$ is used.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.3, p. 135, Eqs. (61)-(62). The source prints $|U_{\beta j}|^4|U_{\alpha j}|^4$ in the constant term; squaring the amplitude gives $|U_{\beta j}|^2|U_{\alpha j}|^2$, which is what is formalized.

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

namespace LipariNeutrino

theorem three_flavor_prob_expansion (U : Matrix (Fin 3) (Fin 3) ℂ) (m2 : Fin 3 → ℝ) (L E : ℝ)
    (α β : Fin 3) :
    oscProb U m2 L E α β =
      (∑ j : Fin 3, ‖U β j‖ ^ 2 * ‖U α j‖ ^ 2) +
      ∑ j : Fin 3, ∑ k : Fin 3,
        if j < k then
          2 * (star (U β j) * U β k * U α j * star (U α k)).re *
              Real.cos ((m2 k - m2 j) * L / (2 * E)) +
            2 * (star (U β j) * U β k * U α j * star (U α k)).im *
              Real.sin ((m2 k - m2 j) * L / (2 * E))
        else 0 := by sorry

end LipariNeutrino
