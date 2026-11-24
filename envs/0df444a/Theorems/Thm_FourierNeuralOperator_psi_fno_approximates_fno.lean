-- Prove2me | Theorems.Thm_FourierNeuralOperator_psi_fno_approximates_fno
-- name    : FourierNeuralOperator.psi_fno_approximates_fno
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:39:00.497731+00:00
-- url     : https://prove2.me/theorems/7f8a6e27-a5e7-4048-abe1-dada63da6998
-- title:
--   Theorem 2.14: $\Psi$-FNOs approximate FNOs of finite width
-- statement:
--   Let $\sigma\in C^m$ be globally Lipschitz, let $s>d/2$ and $m>s$. Let $\hat{\mathcal N}:H^s(\mathbb T^d;\mathbb R^{d_a})\to L^2(\mathbb T^d;\mathbb R^{d_u})$ be an FNO of finite width. Then for all $\varepsilon,B>0$ there are $N\in\mathbb N$ and a $\Psi$-FNO $\mathcal N:L^2_N\to L^2_N$ (with the same activation) such that
--
--   $$\sup_{\|a\|_{H^s}\le B}\|\hat{\mathcal N}(a)-\mathcal N(a)\|_{L^2}\le\varepsilon.$$
--
--   **Formalization Note** A $\Psi$-FNO evaluates its input on the grid, so each $a\in H^s$ ($s>d/2$) is taken to be its continuous representative: the supremum runs over $a\in H^s$ continuous on $[0,2\pi]^d$.
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Section 2.5, Theorem 2.14, p. 11; proof in Appendix D.5, pp. 40-42

import Mathlib
import Definitions.Def_FourierNeuralOperator_Basic

open MeasureTheory Filter Topology

namespace FourierNeuralOperator

theorem psi_fno_approximates_fno {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu]
    (σ : ℝ → ℝ) (m : ℕ) (hσm : ContDiff ℝ m σ) (hσL : ∃ L : NNReal, LipschitzWith L σ)
    (s : ℝ) (hs : (d : ℝ) / 2 < s) (hm : s < m) (Nhat : FNO d ιa ιu)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ Np : PsiFNO d ιa ιu, ∀ a : TorusFun d ιa, MemSobolev s a → ContinuousOn a (torusBox d) →
      sobolevNorm s a ≤ ENNReal.ofReal B →
        l2Norm (Nhat.eval σ a - Np.eval σ a) ≤ ENNReal.ofReal ε := by sorry

end FourierNeuralOperator
