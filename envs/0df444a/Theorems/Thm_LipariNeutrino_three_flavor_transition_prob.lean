-- Prove2me | Theorems.Thm_LipariNeutrino_three_flavor_transition_prob
-- name    : LipariNeutrino.three_flavor_transition_prob
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T12:07:20.930712+00:00
-- url     : https://prove2.me/theorems/8e2734c2-79b9-40be-9577-942fa6f6fafd
-- title:
--   Three-flavour vacuum oscillation probability with the Jarlskog term
-- statement:
--   Let $U$ be a unitary complex $3\times3$ matrix (rows: flavours $\alpha$, columns: mass eigenstates $j=1,2,3$), let $m_1^2,m_2^2,m_3^2$ be real, $L$ a path length and $E$ an energy, and write $\Delta m^2_{jk}=m_k^2-m_j^2$. Let
--
--   $$P(\nu_\alpha\to\nu_\beta)=\Bigl|\sum_j U_{\beta j}U^*_{\alpha j}e^{-im_j^2L/(2E)}\Bigr|^2,\quad A^{jk}_{\alpha\beta}=-4\,\mathrm{Re}\bigl[U_{\alpha j}U^*_{\beta j}U^*_{\alpha k}U_{\beta k}\bigr],\quad J^{\alpha\beta}_{jk}=-\mathrm{Im}\bigl[U_{\alpha j}U^*_{\alpha k}U^*_{\beta j}U_{\beta k}\bigr].$$
--
--   Then for all flavours $\alpha\neq\beta$,
--
--   $$P(\nu_\alpha\to\nu_\beta)=A^{12}_{\alpha\beta}\sin^2\frac{\Delta m^2_{12}L}{4E}+A^{23}_{\alpha\beta}\sin^2\frac{\Delta m^2_{23}L}{4E}+A^{13}_{\alpha\beta}\sin^2\frac{\Delta m^2_{13}L}{4E}-8\,J^{\alpha\beta}_{12}\,\sin\frac{\Delta m^2_{12}L}{4E}\,\sin\frac{\Delta m^2_{23}L}{4E}\,\sin\frac{\Delta m^2_{13}L}{4E}.$$
--
--   This is the general three-flavour vacuum transition probability: a CP-even part with three oscillation amplitudes and a single CP/T-odd term proportional to the Jarlskog coefficient.
--
--   **Formalization Note** The source writes the last term as $\pm 8J$; here the sign is fixed by writing $-8J^{\alpha\beta}_{12}$, which equals $-8J$ for $(\alpha,\beta)=(e,\mu),(\mu,\tau),(\tau,e)$ and $+8J$ for the reversed pairs. Indices $e,\mu,\tau$ and $1,2,3$ are $0,1,2$. No condition on $E$ is imposed (for $E=0$ all phases vanish under Lean's $x/0=0$ and both sides are $0$).
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.3, p. 136, Eq. (71) with notation (62), (73). The printed '$\pm 8J$' is made explicit as $-8J^{\alpha\beta}_{12}$; by Eqs. (65), (68), (69) this is $-8J$ for $(\alpha,\beta)\in\{(e,\mu),(\mu,\tau),(\tau,e)\}$ and $+8J$ for the reversed pairs.

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

namespace LipariNeutrino

theorem three_flavor_transition_prob (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) (m2 : Fin 3 → ℝ) (L E : ℝ)
    (α β : Fin 3) (hαβ : α ≠ β) :
    oscProb U m2 L E α β =
      ampCoeff U α β 0 1 * Real.sin ((m2 1 - m2 0) * L / (4 * E)) ^ 2 +
      ampCoeff U α β 1 2 * Real.sin ((m2 2 - m2 1) * L / (4 * E)) ^ 2 +
      ampCoeff U α β 0 2 * Real.sin ((m2 2 - m2 0) * L / (4 * E)) ^ 2 -
      8 * jarlskogCoeff U α β 0 1 *
        Real.sin ((m2 1 - m2 0) * L / (4 * E)) *
        Real.sin ((m2 2 - m2 1) * L / (4 * E)) *
        Real.sin ((m2 2 - m2 0) * L / (4 * E)) := by sorry

end LipariNeutrino
