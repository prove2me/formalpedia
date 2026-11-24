-- Prove2me | Theorems.Thm_FourierNeuralOperator_psi_fno_universal_approximation
-- name    : FourierNeuralOperator.psi_fno_universal_approximation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:39:52.709376+00:00
-- url     : https://prove2.me/theorems/e8c52d26-3c42-4228-840b-055f75670f52
-- title:
--   Theorem 2.15 (as proved): universal approximation by $\Psi$-FNOs
-- statement:
--   Let $\sigma$ satisfy Assumption 2.4, let $s>d/2$ and $s'\ge0$. Assume in addition that $\sigma\in C^m$ for an integer $m>\max(s',d/2)$. Let $G:H^s(\mathbb T^d;\mathbb R^{d_a})\to H^{s'}(\mathbb T^d;\mathbb R^{d_u})$ be continuous and let $K\subset H^s(\mathbb T^d;\mathbb R^{d_a})$ be compact. Then for every $\varepsilon>0$ there are $N\in\mathbb N$ and a $\Psi$-FNO $\mathcal N:L^2_N\to L^2_N$ such that
--
--   $$\sup_{a\in K}\|G(a)-\mathcal N(a)\|_{H^{s'}}\le\varepsilon.$$
--
--   This is the universality of the implementable, pseudo-spectral form of FNOs.
--
--   **Formalization Note** The hypothesis $\sigma\in C^m$ with $m>\max(s',d/2)$ is not in the printed theorem. The proof uses Theorem 2.14 (which needs $\sigma\in C^m$ with $m>\tilde s>d/2$) and Lemma 2.16 (which needs $m>s'$), and Assumption 2.4 gives only $\sigma\in C^3$. The elements of $K$ are taken continuous on $[0,2\pi]^d$, i.e. they are the continuous representatives.
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Section 2.5, Theorem 2.15, p. 11; proof on p. 11 and in Appendices D.5-D.6

import Mathlib
import Definitions.Def_FourierNeuralOperator_Basic

open MeasureTheory Filter Topology

namespace FourierNeuralOperator

theorem psi_fno_universal_approximation {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu]
    (σ : ℝ → ℝ) (hσ : IsActivation σ) (s s' : ℝ) (hs : (d : ℝ) / 2 < s) (hs' : 0 ≤ s')
    (m : ℕ) (hm₁ : s' < m) (hm₂ : (d : ℝ) / 2 < m) (hσm : ContDiff ℝ m σ)
    (G : TorusFun d ιa → TorusFun d ιu) (hG : SobolevContinuous s s' G)
    (K : Set (TorusFun d ιa)) (hK : IsSobolevCompact s K)
    (hKc : ∀ a ∈ K, ContinuousOn a (torusBox d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ Np : PsiFNO d ιa ιu, ∀ a ∈ K, sobolevNorm s' (G a - Np.eval σ a) ≤ ENNReal.ofReal ε := by sorry

end FourierNeuralOperator
