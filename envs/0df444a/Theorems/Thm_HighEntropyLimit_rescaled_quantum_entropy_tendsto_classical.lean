-- Prove2me | Theorems.Thm_HighEntropyLimit_rescaled_quantum_entropy_tendsto_classical
-- name    : HighEntropyLimit.rescaled_quantum_entropy_tendsto_classical
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:09:28.813979+00:00
-- url     : https://prove2.me/theorems/ae8cfed1-5ea1-4ba2-8724-fcead9167ec9
-- title:
--   High-entropy limit: $S_Q(\lambda\Sigma)-\ln\lambda \to S_C(\Sigma)$
-- statement:
--   Let $\hbar>0$ and $\Sigma>0$. Let $S_Q$ be the von Neumann entropy of a Gaussian state with uncertainty $\Sigma$ and $S_C$ the classical Gaussian entropy. Then
--   $$\lim_{\lambda\to\infty}\Big(S_Q(\lambda\Sigma) - \ln\lambda\Big) = \ln\frac{\Sigma}{\hbar} + 1 = S_C(\Sigma).$$
--
--   This is the paper's quantitative high-entropy limit. Shrinking the pure-state uncertainty from $\hbar$ to $\hbar/\lambda$ and shifting the zero of entropy by $\ln\lambda$ turns the quantum entropy–uncertainty curve into the classical one as $\lambda\to\infty$. Mathematically this is equivalent to $\hbar\to0$.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 11, Section 4.3: 'The entropy will become S^λ_Q(Σ) = S_Q(λΣ) − ln(λ) ... If one takes the limit λ → ∞, the above expression reduces to the classical equation' (Fig. 3); with Eqs. (2),(3) p. 3

import Mathlib
import Definitions.Def_HighEntropyLimit_gaussian_entropy
open Filter Topology

namespace HighEntropyLimit
theorem rescaled_quantum_entropy_tendsto_classical (hbar Sig : ℝ) (hhbar : 0 < hbar)
    (hSig : 0 < Sig) :
    Tendsto (fun lam : ℝ => rescaledQuantumGaussianEntropy hbar lam Sig) atTop
      (𝓝 (classicalGaussianEntropy hbar Sig)) := by sorry
end HighEntropyLimit
