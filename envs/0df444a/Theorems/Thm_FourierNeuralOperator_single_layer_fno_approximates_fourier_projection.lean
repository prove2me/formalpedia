-- Prove2me | Theorems.Thm_FourierNeuralOperator_single_layer_fno_approximates_fourier_projection
-- name    : FourierNeuralOperator.single_layer_fno_approximates_fourier_projection
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:35:28.508842+00:00
-- url     : https://prove2.me/theorems/476454e1-5d57-44b0-a310-ec5aec2a5766
-- title:
--   Lemma D.1: a single FNO layer approximates the Fourier projection in $H^{s'}$
-- statement:
--   Let $\sigma$ satisfy Assumption 2.4 and let $\sigma\in C^m$ for an integer $m>s'$, where $s'\ge0$. Let $N\in\mathbb N$ and let $K\subset H^{s'}(\mathbb T^d;\mathbb R^{\iota})$ be compact. Then for every $\varepsilon>0$ there is a single-layer FNO $\mathcal L$ (depth $1$) mapping $H^{s'}$ into $H^{s'}$ such that
--
--   $$\sup_{v\in K}\|P_Nv-\mathcal L(v)\|_{H^{s'}}\le\varepsilon,$$
--
--   where $P_N$ is the Fourier projection onto modes $|k|_\infty\le N$.
--
--   This is the device that turns an $L^2$-approximation into an $H^{s'}$-approximation in Lemmas 2.6 and 2.16.
--
--   **Formalization Note** The paper's Lemma D.1 lists only $\sigma\in C^m$; the standing Assumption 2.4 (which supplies $\sigma'(x_0)\ne0$ for some $x_0$, used in the proof) is written as a hypothesis.
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Appendix D.1, Lemma D.1, p. 31

import Mathlib
import Definitions.Def_FourierNeuralOperator_Basic

open MeasureTheory Filter Topology

namespace FourierNeuralOperator

theorem single_layer_fno_approximates_fourier_projection {d : ℕ} {ι : Type} [Fintype ι]
    (σ : ℝ → ℝ) (hσ : IsActivation σ) (s' : ℝ) (hs' : 0 ≤ s') (N : ℕ)
    (m : ℕ) (hm : s' < m) (hσm : ContDiff ℝ m σ)
    (K : Set (TorusFun d ι)) (hK : IsSobolevCompact s' K) (ε : ℝ) (hε : 0 < ε) :
    ∃ Nn : FNO d ι ι, Nn.depth = 1 ∧
      (∀ v, MemSobolev s' v → MemSobolev s' (Nn.eval σ v)) ∧
      ∀ v ∈ K, sobolevNorm s' (fourierProj N v - Nn.eval σ v) ≤ ENNReal.ofReal ε := by sorry

end FourierNeuralOperator
