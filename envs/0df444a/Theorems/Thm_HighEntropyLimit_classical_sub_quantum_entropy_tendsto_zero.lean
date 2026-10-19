-- Prove2me | Theorems.Thm_HighEntropyLimit_classical_sub_quantum_entropy_tendsto_zero
-- name    : HighEntropyLimit.classical_sub_quantum_entropy_tendsto_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:55:07.376984+00:00
-- url     : https://prove2.me/theorems/7586ea03-c498-47b7-ad9d-214c9f598313
-- title:
--   Classical and quantum Gaussian entropies agree at large uncertainty
-- statement:
--   Let $\hbar>0$. The classical and quantum Gaussian entropies have the same asymptotics:
--   $$\lim_{\Sigma\to\infty}\big(S_C(\Sigma) - S_Q(\Sigma)\big) = 0.$$
--
--   This is the 'convergent prediction at high entropy' shown by the dashed difference curve in Fig. 2.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 4, Fig. 2 and the following paragraph ('The convergent prediction at high entropy ...')

import Mathlib
import Definitions.Def_HighEntropyLimit_gaussian_entropy
open Filter Topology

namespace HighEntropyLimit
theorem classical_sub_quantum_entropy_tendsto_zero (hbar : ℝ) (hhbar : 0 < hbar) :
    Tendsto (fun Sig : ℝ => classicalGaussianEntropy hbar Sig - quantumGaussianEntropy hbar Sig)
      atTop (𝓝 0) := by sorry
end HighEntropyLimit
