-- Prove2me | Theorems.Thm_FourierNeuralOperator_fno_universal_reduction_to_l2
-- name    : FourierNeuralOperator.fno_universal_reduction_to_l2
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:36:28.314495+00:00
-- url     : https://prove2.me/theorems/1ffe3293-4950-41f3-9784-d77dfb7dc386
-- title:
--   Lemma 2.6 (as proved): universal approximation into $L^2$ implies universal approximation into $H^{s'}$
-- statement:
--   Let $\sigma$ satisfy Assumption 2.4 and let $s,s'\ge0$. Assume in addition that $\sigma\in C^m$ for some integer $m>s'$. If FNOs with activation $\sigma$ are universal approximators of continuous operators $H^s(\mathbb T^d;\mathbb R^{d_a})\to L^2(\mathbb T^d;\mathbb R^{d_u})$ (Theorem 2.5 with $s'=0$), then they are universal approximators of continuous operators $H^s\to H^{s'}$. That is, for every continuous $G:H^s\to H^{s'}$, compact $K\subset H^s$ and $\varepsilon>0$, there is an FNO $\mathcal N$, continuous as an operator $H^s\to H^{s'}$, with $\sup_{a\in K}\|G(a)-\mathcal N(a)\|_{H^{s'}}\le\varepsilon$.
--
--   **Formalization Note** The hypothesis $\sigma\in C^m$, $m>s'$, is not in the printed lemma. The proof (Appendix D.1) uses it through Lemma D.1, and Assumption 2.4 gives only $\sigma\in C^3$.
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Section 2.4, Lemma 2.6, p. 6; proof in Appendix D.1, pp. 31-33

import Mathlib
import Definitions.Def_FourierNeuralOperator_Basic

open MeasureTheory Filter Topology

namespace FourierNeuralOperator

theorem fno_universal_reduction_to_l2 {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu]
    (σ : ℝ → ℝ) (hσ : IsActivation σ) (s s' : ℝ) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (m : ℕ) (hm : s' < m) (hσm : ContDiff ℝ m σ) :
    UniversalApproxFNO σ d ιa ιu s 0 → UniversalApproxFNO σ d ιa ιu s s' := by sorry

end FourierNeuralOperator
