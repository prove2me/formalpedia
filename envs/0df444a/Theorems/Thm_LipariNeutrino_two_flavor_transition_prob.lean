-- Prove2me | Theorems.Thm_LipariNeutrino_two_flavor_transition_prob
-- name    : LipariNeutrino.two_flavor_transition_prob
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T05:01:32.284987+00:00
-- url     : https://prove2.me/theorems/98ce1353-ae78-4d8a-9d89-e8e64d93ce1c
-- title:
--   Two-flavour oscillation probability $\sin^2 2\theta\,\sin^2(\Delta m^2 L/4E)$
-- statement:
--   Consider two neutrino flavours $\nu_e,\nu_\mu$ and two mass eigenstates $\nu_1,\nu_2$ with squared masses $m_1^2, m_2^2$, related by the rotation matrix
--
--   $$U(\theta)=\begin{pmatrix}\cos\theta & \sin\theta\\ -\sin\theta & \cos\theta\end{pmatrix}.$$
--
--   For a neutrino of energy $E$ travelling a distance $L$, let $P(\nu_e\to\nu_\mu)=\bigl|\sum_{j} U_{\mu j}U_{ej}^{*}e^{-i m_j^2 L/(2E)}\bigr|^2$. Then
--
--   $$P(\nu_e\to\nu_\mu)=\sin^2(2\theta)\,\sin^2\!\left(\frac{(m_2^2-m_1^2)\,L}{4E}\right).$$
--
--   This is the basic two-flavour oscillation formula: the amplitude of the oscillation is $\sin^2 2\theta$ and its length is set by $\Delta m^2/E$.
--
--   **Formalization Note** Flavour index $e\mapsto 0$, $\mu\mapsto 1$ and mass index $1\mapsto 0$, $2\mapsto 1$. No sign condition on $E$ is imposed; for $E=0$ Lean's convention $x/0=0$ makes every phase zero and both sides vanish.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.1, p. 131-132, Eq. (52) (with the relativistic identification $L \simeq t$).

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability
import Definitions.Def_LipariNeutrino_MixingMatrices

namespace LipariNeutrino

theorem two_flavor_transition_prob (θ : ℝ) (m2 : Fin 2 → ℝ) (L E : ℝ) :
    oscProb (twoFlavorMix θ) m2 L E 0 1 =
      Real.sin (2 * θ) ^ 2 * Real.sin ((m2 1 - m2 0) * L / (4 * E)) ^ 2 := by sorry

end LipariNeutrino
