-- Prove2me | Theorems.Thm_LipariNeutrino_jarlskog_pmns
-- name    : LipariNeutrino.jarlskog_pmns
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T11:36:37.826951+00:00
-- url     : https://prove2.me/theorems/7a71268b-cd34-474f-ae50-276d1927d152
-- title:
--   Jarlskog parameter in the standard parametrization
-- statement:
--   Let $U=U(\theta_{12},\theta_{13},\theta_{23},\delta)$ be the standard parametrization of the lepton mixing matrix,
--
--   $$U=\begin{pmatrix}1&0&0\\0&c_{23}&s_{23}\\0&-s_{23}&c_{23}\end{pmatrix}\begin{pmatrix}c_{13}&0&s_{13}e^{-i\delta}\\0&1&0\\-s_{13}e^{i\delta}&0&c_{13}\end{pmatrix}\begin{pmatrix}c_{12}&s_{12}&0\\-s_{12}&c_{12}&0\\0&0&1\end{pmatrix},\qquad c_{jk}=\cos\theta_{jk},\ s_{jk}=\sin\theta_{jk}.$$
--
--   Then for all real $\theta_{12},\theta_{13},\theta_{23},\delta$,
--
--   $$J^{e\mu}_{12}=-\mathrm{Im}\bigl[U_{e1}U^*_{e2}U^*_{\mu1}U_{\mu2}\bigr]=-\,c_{13}^2\,s_{13}\,s_{12}\,c_{12}\,s_{23}\,c_{23}\,\sin\delta.$$
--
--   This expresses the Jarlskog parameter in terms of the mixing angles and the CP phase, and shows that CP violation in vacuum requires $\delta\notin\{0,\pi\}$ and all three angles nonzero.
--
--   **Formalization Note** The printed Eq. (70) has no leading minus sign. With the source's own matrix (57) and its definition (69) of $J$ taken literally, the value carries an overall minus sign (a numerical check, e.g. $\theta_{12}=0.3,\theta_{13}=0.2,\theta_{23}=0.7,\delta=1.1$, gives $J^{e\mu}_{12}\approx-0.02366$ while the printed product is $\approx+0.02366$). The formal statement uses the sign that follows from (57) and (69).
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.2-4.3, pp. 134 and 136, Eqs. (57), (69), (70). SIGN CAVEAT: with the source's own definitions (57) and (69), $J^{e\mu}_{12}$ equals MINUS the product printed in (70) (checked numerically, not formally); the formal statement carries the minus sign.

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability
import Definitions.Def_LipariNeutrino_MixingMatrices

namespace LipariNeutrino

theorem jarlskog_pmns (θ12 θ13 θ23 δ : ℝ) :
    jarlskogCoeff (pmns θ12 θ13 θ23 δ) 0 1 0 1 =
      -(Real.cos θ13 ^ 2 * Real.sin θ13 * Real.sin θ12 * Real.cos θ12 *
          Real.sin θ23 * Real.cos θ23 * Real.sin δ) := by sorry

end LipariNeutrino
