-- Prove2me | Theorems.Thm_FourierNeuralOperator_psi_fno_universal_reduction_to_l2
-- name    : FourierNeuralOperator.psi_fno_universal_reduction_to_l2
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:39:23.367853+00:00
-- url     : https://prove2.me/theorems/05be415f-cd80-4e02-bb9f-365aaf8c277b
-- title:
--   Lemma 2.16 (as proved): universal approximation by $\Psi$-FNOs into $L^2$ implies it into $H^{s'}$
-- statement:
--   Let $\sigma$ satisfy Assumption 2.4, let $s>d/2$ and $s'\ge0$. Assume in addition that $\sigma\in C^m$ for an integer $m>\max(s',d/2)$. Suppose that for every continuous $G:H^s\to L^2$, compact $K\subset H^s$ and $\varepsilon>0$ there is $\tilde N_0$ such that for every $N\ge\tilde N_0$ some $\Psi$-FNO $\mathcal N:L^2_N\to L^2_N$ satisfies $\sup_{a\in K}\|G(a)-\mathcal N(a)\|_{L^2}\le\varepsilon$. Then for every continuous $G:H^s\to H^{s'}$, compact $K\subset H^s$ and $\varepsilon>0$ there is $N_0$ such that for every $N\ge N_0$ some $\Psi$-FNO $\hat{\mathcal N}:L^2_N\to L^2_N$ satisfies
--
--   $$\sup_{a\in K}\|G(a)-\hat{\mathcal N}(a)\|_{H^{s'}}\le\varepsilon.$$
--
--   **Formalization Note** The printed lemma reads "Assume Theorem 2.15 holds for $s'=0$; then it holds for arbitrary $s'$". Theorem 2.15 gives a single $N$, but the proof (Appendix D.6) assumes and proves the statement for all $N\ge N_0$, and it is stated in that form. The proof also uses $\sigma\in C^m$ with $m>\max(s',d/2)$ through Lemma D.1, which Assumption 2.4 does not supply. The elements of $K$ are taken continuous on $[0,2\pi]^d$, i.e. they are the continuous representatives.
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Section 2.5, Lemma 2.16, p. 11; proof in Appendix D.6, pp. 42-43

import Mathlib
import Definitions.Def_FourierNeuralOperator_Basic

open MeasureTheory Filter Topology

namespace FourierNeuralOperator

theorem psi_fno_universal_reduction_to_l2 {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu]
    (σ : ℝ → ℝ) (hσ : IsActivation σ) (s s' : ℝ) (hs : (d : ℝ) / 2 < s) (hs' : 0 ≤ s')
    (m : ℕ) (hm₁ : s' < m) (hm₂ : (d : ℝ) / 2 < m) (hσm : ContDiff ℝ m σ) :
    UniversalApproxPsiFNO σ d ιa ιu s 0 → UniversalApproxPsiFNO σ d ιa ιu s s' := by sorry

end FourierNeuralOperator
