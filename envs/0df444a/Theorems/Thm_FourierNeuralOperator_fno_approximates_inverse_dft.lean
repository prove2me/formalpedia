-- Prove2me | Theorems.Thm_FourierNeuralOperator_fno_approximates_inverse_dft
-- name    : FourierNeuralOperator.fno_approximates_inverse_dft
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:37:54.450738+00:00
-- url     : https://prove2.me/theorems/8efe7200-cb86-439c-95f4-d627006cdfc0
-- title:
--   Lemma 2.8: an FNO approximates the inverse discrete Fourier transform
-- statement:
--   Let $\sigma$ satisfy Assumption 2.4, and let $B>0$ and $N\in\mathbb N$. For every $\varepsilon>0$ there is an FNO $\mathcal N:L^2(\mathbb T^d;\mathbb R^{2\mathcal K_N})\to L^2(\mathbb T^d)$ such that for every real trigonometric polynomial $v\in L^2_N(\mathbb T^d)$ with $\|v\|_{L^2}\le B$,
--
--   $$\|v-\mathcal N(w)\|_{L^2}\le\varepsilon,$$
--
--   where $w(x):=\{(\mathrm{Re}(\hat v_k),\mathrm{Im}(\hat v_k))\}_{k\in\mathcal K_N}$ is the constant function collecting the real and imaginary parts of the Fourier coefficients of $v$.
--
--   **Formalization Note** $v\in L^2_N$ is taken as a function that equals a trigonometric polynomial of degree $\le N$ at every point.
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Section 2.4, Lemma 2.8, p. 7; proof in Appendix D.3, pp. 35-36

import Mathlib
import Definitions.Def_FourierNeuralOperator_Basic

open MeasureTheory Filter Topology

namespace FourierNeuralOperator

theorem fno_approximates_inverse_dft {d : ℕ} (σ : ℝ → ℝ) (hσ : IsActivation σ)
    (B : ℝ) (hB : 0 < B) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Nn : FNO d (Fin 2 × freqBox d N) (Fin 1),
      ∀ v : TorusFun d (Fin 1), IsTrigPoly N v → l2Norm v ≤ ENNReal.ofReal B →
        l2Norm (v - Nn.eval σ (fun _ p =>
          if p.1 = 0 then (fourierCoeff v p.2.1 0).re else (fourierCoeff v p.2.1 0).im))
          ≤ ENNReal.ofReal ε := by sorry

end FourierNeuralOperator
