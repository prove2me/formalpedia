-- Prove2me | Theorems.Thm_FourierNeuralOperator_fno_approximates_fourier_coefficients
-- name    : FourierNeuralOperator.fno_approximates_fourier_coefficients
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:37:21.888575+00:00
-- url     : https://prove2.me/theorems/531246a8-b772-4bc9-a3f1-16c652716864
-- title:
--   Lemma 2.7: an FNO approximates the Fourier coefficients $\hat v_k$, $|k|_\infty\le N$
-- statement:
--   Let $\sigma$ satisfy Assumption 2.4, and let $B>0$ and $N\in\mathbb N$. For every $\varepsilon>0$ there is an FNO $\mathcal N:L^2(\mathbb T^d)\to L^2(\mathbb T^d;\mathbb R^{2\mathcal K_N})$, $v\mapsto\{\mathcal N(v)_{\ell,k}\}_{\ell\in\{1,2\},k\in\mathcal K_N}$, whose output functions are constant in $x\in\mathbb T^d$ for every input $v\in L^2(\mathbb T^d)$, such that for every real $v\in L^2(\mathbb T^d)$ with $\|v\|_{L^2}\le B$ and every $k\in\mathbb Z^d$ with $|k|_\infty\le N$,
--
--   $$\|\mathrm{Re}(\hat v_k)-\mathcal N(v)_{1,k}\|_{L^\infty}\le\varepsilon,\qquad\|\mathrm{Im}(\hat v_k)-\mathcal N(v)_{2,k}\|_{L^\infty}\le\varepsilon.$$
--
--   **Formalization Note** The output is constant at every point, so the $L^\infty$ bounds are written pointwise for every $x$. The components $\ell=1,2$ are indexed by $0,1$.
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Section 2.4, Lemma 2.7, p. 6; proof in Appendix D.2, pp. 33-35

import Mathlib
import Definitions.Def_FourierNeuralOperator_Basic

open MeasureTheory Filter Topology

namespace FourierNeuralOperator

theorem fno_approximates_fourier_coefficients {d : ℕ} (σ : ℝ → ℝ) (hσ : IsActivation σ)
    (B : ℝ) (hB : 0 < B) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Nn : FNO d (Fin 1) (Fin 2 × freqBox d N),
      (∀ v : TorusFun d (Fin 1), MemL2 v → ∀ x y, Nn.eval σ v x = Nn.eval σ v y) ∧
      ∀ v : TorusFun d (Fin 1), MemL2 v → l2Norm v ≤ ENNReal.ofReal B →
        ∀ (k : freqBox d N) (x : Fin d → ℝ),
          |(fourierCoeff v k.1 0).re - Nn.eval σ v x (0, k)| ≤ ε ∧
          |(fourierCoeff v k.1 0).im - Nn.eval σ v x (1, k)| ≤ ε := by sorry

end FourierNeuralOperator
