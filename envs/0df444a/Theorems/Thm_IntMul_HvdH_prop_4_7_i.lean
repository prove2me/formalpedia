-- Prove2me | Theorems.Thm_IntMul_HvdH_prop_4_7_i
-- name    : IntMul.HvdH.prop_4_7_i
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:26:07.674574+00:00
-- url     : https://prove2.me/theorems/cd52bafd-dc27-492c-9d83-aba82ea394e7
-- title:
--   HvdH Prop. 4.7(i): $\mathcal F_s = 2^{2\alpha^2}\mathcal B\mathcal F_t\mathcal A$ with $\|\mathcal A\|,\|\mathcal B\|\le 1$
-- statement:
--   **Gaussian resampling reduces a DFT of length $s$ to one of length $t$** (Harvey–van der Hoeven, Proposition 4.7(i), one-dimensional case).
--
--   Let $s<t$ be coprime positive integers and let $\alpha\ge 2$ be an integer with $\alpha^2\theta\ge 1$, where $\theta = t/s-1$. Write $\mathcal F_n:\mathbb C^n\to\mathbb C^n$ for the normalised DFT $(\mathcal F_n u)_k = \frac1n\sum_{j\in\mathbb Z/n} e^{-2\pi i jk/n}u_j$ (Mathlib's `ZMod.dft` divided by $n$). Then there are linear maps $\mathcal A:\mathbb C^s\to\mathbb C^t$ and $\mathcal B:\mathbb C^t\to\mathbb C^s$, both of operator norm at most $1$ for the sup norm, with
--   $$\mathcal F_s = 2^{2\alpha^2}\,\mathcal B\,\mathcal F_t\,\mathcal A .$$
--
--   In the paper, $\mathcal A=\tfrac12\mathcal S$ is the Gaussian resampling map and $\mathcal B$ is built from the permutations $P_s^{-1},P_t$, the row selection $\mathcal C$, the diagonal $\mathcal D$ and the inverse of $\mathcal N=\mathcal C\mathcal T\mathcal D = I+\mathcal E$ with $\|\mathcal E\|<2^{-\alpha^2\theta}\le\tfrac12$. The proof formalises the resampling identity (Theorem 4.2) via Poisson summation for Gaussians and Lemma 4.6.
--
--   This is a node in the integer-multiplication-kappa campaign: it is the analytic core of the HvdH $O(n\log n)$ algorithm.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 4.3, Proposition 4.7(i) (one-dimensional case; alpha taken integral), using Theorem 4.2 and Lemmas 4.5, 4.6

import Mathlib

namespace IntMul.HvdH
theorem prop_4_7_i (s t α : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (hα : 2 ≤ α) (hθ : 1 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) :
    ∃ (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ∀ u, (s : ℂ)⁻¹ • ZMod.dft u = (2 : ℂ) ^ (2 * α ^ 2) • B ((t : ℂ)⁻¹ • ZMod.dft (A u)) := by sorry
end IntMul.HvdH
