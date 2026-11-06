-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_values_of_sum_sq_le
-- name    : GuthMaynard.card_le_of_large_values_of_sum_sq_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T19:36:20.369959+00:00
-- url     : https://prove2.me/theorems/be58ac81-b4f9-45c2-bb2f-7865f3b20b33
-- title:
--   The ℓ² form of Guth–Maynard's large values estimate (open)
-- statement:
--   For every $K$ and every $\varepsilon > 0$ there is $T_0$ such that for all $T \ge T_0$, all integers $N \ge 1$, all $V > 0$, all complex $(b_n)$ with $\sum_{N\le n\le 2N}|b_n|^2 \le KN$, and all $t_0, \dots, t_{R-1} \in [0, T]$ with $|t_r - t_s| \ge 1$ for $r \ne s$: if $\big|\sum_{N\le n\le 2N} b_nn^{it_r}\big| \ge V$ for every $r$, then
--   $$R \le T^{\varepsilon}\Big(\frac{N^2}{V^2} + \frac{N^{18/5}}{V^4} + \frac{TN^{12/5}}{V^4}\Big).$$
--
--   This is Guth–Maynard's Theorem 1.1 (the mission goal `GuthMaynard.card_le_of_large_values`, https://prove2.me/theorems/60ec1d12-461f-408f-9d9b-ff3d0d3fa3bf) with the hypothesis $|b_n| \le 1$ replaced by the weaker $\ell^2$ constraint. The paper does not claim it. Its Remark on p. 5 (arXiv:2405.20552v2) says: “Many earlier results on large values of Dirichlet polynomials (such as those stemming from the Mean Value Theorem or the Montgomery-Huxley-Halász large values estimate) allowed one to relax the $\ell^\infty$ constraint $|b_n| \le 1$ on the coefficients to a weaker $\ell^2$ constraint $(\sum_{n=N}^{2N}|b_n|^2)^{1/2} = O(N^{1/2})$. Our argument crucially relies on the stronger $\ell^\infty$ assumption to bound the additive energy $E(W)$ efficiently, and we do not know how to obtain Theorem 1.1 if we only have $\ell^2$ bounds on the coefficients.” For Montgomery's large value conjecture the $\ell^2$ form is known to fail: the paper says (pp. 3–4) that “Bourgain [B5] gave a counterexample to an earlier (stronger) formulation given in terms of the $\ell^2$ norm of the coefficients $b_n$”, citing J. Bourgain, *Remarks on Montgomery's conjectures on Dirichlet sums*, Lecture Notes in Math. 1469 (1991) 153–165, https://doi.org/10.1007/BFb0089222. A proof or a disproof of this statement settles the question.
--
--   **Formalization note.** "$O(N^{1/2})$" is read as a constant $K$ fixed in advance, with the threshold $T_0$ allowed to depend on $K$ and $\varepsilon$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 5, the ℓ² question of the Remark (open; not claimed in the paper)

import Mathlib

namespace GuthMaynard

theorem card_le_of_large_values_of_sum_sq_le (K : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (N : ℕ), 1 ≤ N → ∀ (V : ℝ), 0 < V → ∀ (b : ℕ → ℂ),
      ∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ ^ 2 ≤ K * N →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) → (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ T ^ ε * ((N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 +
        T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  sorry

end GuthMaynard
