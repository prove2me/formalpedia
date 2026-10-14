-- Prove2me | Theorems.Thm_HighEntropyLimit_gaussian_entropy_zero_points
-- name    : HighEntropyLimit.gaussian_entropy_zero_points
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:54:15.086001+00:00
-- url     : https://prove2.me/theorems/49c748ab-8286-4a00-aebb-ea1c986e148b
-- title:
--   Zeros and signs of the Gaussian entropy curves
-- statement:
--   Let $\hbar>0$. Then
--
--   1. $S_Q(\hbar/2) = 0$: the quantum entropy vanishes at the Heisenberg bound;
--   2. $S_Q(\Sigma) > 0$ for every $\Sigma > \hbar/2$;
--   3. $S_C(\hbar/e) = 0$;
--   4. $S_C(\Sigma) < 0$ for every $0 < \Sigma < \hbar/e$.
--
--   So the quantum curve reaches zero at $\hbar/2$, while the classical curve reaches zero at $\hbar/e$ and then continues into negative values.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 3, Section 2.2, text after Eq. (3): 'in quantum mechanics the entropy ... reaches zero at ħ/2 ...; classical mechanics reaches zero entropy for ħ/e, and then continues in the negative region'

import Mathlib
import Definitions.Def_HighEntropyLimit_gaussian_entropy

namespace HighEntropyLimit
theorem gaussian_entropy_zero_points (hbar : ℝ) (hhbar : 0 < hbar) :
    quantumGaussianEntropy hbar (hbar / 2) = 0 ∧
    (∀ Sig : ℝ, hbar / 2 < Sig → 0 < quantumGaussianEntropy hbar Sig) ∧
    classicalGaussianEntropy hbar (hbar / Real.exp 1) = 0 ∧
    (∀ Sig : ℝ, 0 < Sig → Sig < hbar / Real.exp 1 → classicalGaussianEntropy hbar Sig < 0) := by
  sorry
end HighEntropyLimit
