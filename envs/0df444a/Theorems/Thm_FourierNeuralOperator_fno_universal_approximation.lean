-- Prove2me | Theorems.Thm_FourierNeuralOperator_fno_universal_approximation
-- name    : FourierNeuralOperator.fno_universal_approximation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:38:32.188326+00:00
-- url     : https://prove2.me/theorems/d8291f47-50f7-4a71-bff8-01a2074f23b8
-- title:
--   Theorem 2.5 (as proved): universal approximation by Fourier neural operators
-- statement:
--   Let the activation $\sigma$ satisfy Assumption 2.4, and let $s,s'\ge0$. Assume in addition that $\sigma\in C^m$ for some integer $m>s'$. Let $G:H^s(\mathbb T^d;\mathbb R^{d_a})\to H^{s'}(\mathbb T^d;\mathbb R^{d_u})$ be a continuous operator and let $K\subset H^s(\mathbb T^d;\mathbb R^{d_a})$ be compact. Then for every $\varepsilon>0$ there is an FNO $\mathcal N$ of the form (2.6), continuous as an operator $H^s\to H^{s'}$, such that
--
--   $$\sup_{a\in K}\|G(a)-\mathcal N(a)\|_{H^{s'}}\le\varepsilon.$$
--
--   This is the paper's main result. Fourier neural operators approximate every continuous operator between Sobolev spaces on the torus, uniformly on compact sets.
--
--   **Formalization Note** The hypothesis $\sigma\in C^m$ with $m>s'$ is not in the printed theorem, which assumes only Assumption 2.4 ($\sigma\in C^3$). The proof of the case $s'>0$ (Lemma 2.6, via Lemma D.1) uses it. It is automatic for $s'<3$. The FNO produced has finite width (Definition 2.13), as the construction of Appendix D.4 does.
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Section 2.4, Theorem 2.5, p. 5; proof in Appendix D.4, pp. 36-40, and Appendix D.1

import Mathlib
import Definitions.Def_FourierNeuralOperator_Basic

open MeasureTheory Filter Topology

namespace FourierNeuralOperator

theorem fno_universal_approximation {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu]
    (σ : ℝ → ℝ) (hσ : IsActivation σ) (s s' : ℝ) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (m : ℕ) (hm : s' < m) (hσm : ContDiff ℝ m σ)
    (G : TorusFun d ιa → TorusFun d ιu) (hG : SobolevContinuous s s' G)
    (K : Set (TorusFun d ιa)) (hK : IsSobolevCompact s K) (ε : ℝ) (hε : 0 < ε) :
    ∃ Nn : FNO d ιa ιu, SobolevContinuous s s' (Nn.eval σ) ∧
      ∀ a ∈ K, sobolevNorm s' (G a - Nn.eval σ a) ≤ ENNReal.ofReal ε := by sorry

end FourierNeuralOperator
