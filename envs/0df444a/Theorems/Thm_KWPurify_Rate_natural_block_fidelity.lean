-- Prove2me | Theorems.Thm_KWPurify_Rate_natural_block_fidelity
-- name    : KWPurify.Rate.natural_block_fidelity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:49.278109+00:00
-- url     : https://prove2.me/theorems/92d91906-fdd8-4d93-b35d-d647729288ac
-- title:
--   p. 14, §4.3 — $\rho_s(\beta)$ is normalized and $\operatorname{tr}(\sigma^{\otimes 2s}\rho_s(\beta)) = (1-e^{-2\beta})/(1-e^{-(4s+2)\beta})$
-- statement:
--   Let $\beta > 0$, $n = 2s \in \mathbb N$, $\psi = (1,0) \in \mathbb C^2$ and $\sigma_0 = |\psi\rangle\langle\psi|$. Let $\rho_s(\beta) = \frac{\sinh\beta}{\sinh((n+1)\beta)} S_n e^{2\beta L_3}$ be the Bose-space state on $n$ qubits. Then $\operatorname{tr}\rho_s(\beta) = 1$ and
--   $$\operatorname{tr}\big(\sigma_0^{\otimes n}\,\rho_s(\beta)\big) = \frac{1-e^{-2\beta}}{1-e^{-(2n+2)\beta}} = \frac{1-e^{-2\beta}}{1-e^{-(4s+2)\beta}}.$$
--
--   This is the all-qubit fidelity of one block of the natural purifier (which keeps the $2s$ qubits of the symmetric part); it is also, up to the factor $(2s+1)/(M+1)$, the cloning branch of the closed form $f_{\mathrm{all}}$.
--
--   **Formalization Note** The normalization $\operatorname{tr}\rho_s(\beta)=1$ is stated on p. 8 ("The $\rho_s(\beta)$ are normalized"); it is included here as a check of the definition. On the page the middle denominator of the display is misprinted as $e^{(2s+1)\beta} - e^{(2s+1)\beta}$; the outer equality, stated here, is the correct one.
-- source:
--   Keyl & Werner, The Rate of Optimal Purification procedures, arXiv:quant-ph/9910124v1, p. 14, §4.3, first display (and p. 8: tr ρ_s(β) = 1)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_KWPurify_Rate_Blocks

namespace KWPurify.Rate
theorem natural_block_fidelity (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    (boseState β n).trace = 1 ∧
    (QAlgorithms.piKron n psiDensity * boseState β n).trace.re =
      (1 - Real.exp (-2 * β)) / (1 - Real.exp (-(2 * (n : ℝ) + 2) * β)) := by sorry
end KWPurify.Rate
