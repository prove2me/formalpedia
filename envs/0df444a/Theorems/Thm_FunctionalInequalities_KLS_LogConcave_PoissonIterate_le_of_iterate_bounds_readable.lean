-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_le_of_iterate_bounds_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.le_of_iterate_bounds_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:28.537982+00:00
-- url     : https://prove2.me/theorems/f80538b2-5d61-41ae-9ced-cdc9bb4e7bf2
-- title:
--   Iterate Bounds Imply the Final Criterion
-- statement:
--   This formalizes the final real-sequence argument of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 17, in the operator route.
--
--   Let $C,c,R\in\mathbb R$, sequences $v,p,\chi,L,\alpha:\mathbb N\to\mathbb R$, and $t:\mathbb N\to\mathbb N\to\mathbb R$ be given. Assume:
--
--   1. $C>0$, $c\ge1$, and $R\ge1$; $v_k\ge0$, $C^{-1}\le v_0$, and $v_k\to0$.
--   2. For every $N$, $v_0=v_N+\sum_{k<N}p_k$.
--   3. $\chi_k\ge0$, $\sum_{k<N}\chi_k\le L_0$, and $L_0\le((11/10)C^{-1})^2$.
--   4. $L_{k+1}\le L_k$ and $L_{k+1}=\alpha_k^2v_{k+1}$.
--   5. $\alpha_k\ge0$, $\alpha_k=0$ implies $v_{k+1}=0$, and $\alpha_k>0$ implies $C^{-1}\le\alpha_k^2$.
--   6. $t_{d,k}\ge0$, $t_{d,k}\le R^{2d}v_{k+1}$ for $d\ge1$, and the recursion bound from (63) holds whenever $2d\le k+1$ and all earlier scales are positive with square at most $3/C$.
--   7. For every $N$, if $\alpha_j^2\le3/C$ whenever $j+1<N$, then
--      $$\sum_{k<N}p_k\le L_0+\frac3C\sum_{k<N-1}t_{1,k}.$$
--
--   Then
--
--   $$C\le100c^2R^2.$$
--
--   This is the scalar terminal estimate that converts the iterate identities, Taylor bounds, and defect recursion into a Poincaré-constant bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem le_of_iterate_bounds {C c R : ℝ} {v p χ L α : ℕ → ℝ} {t : ℕ → ℕ → ℝ}
--       (hC : 0 < C) (hc : 1 ≤ c) (hR : 1 ≤ R)
--       (hv : ∀ k, 0 ≤ v k) (hv0 : C⁻¹ ≤ v 0) (hvlim : Tendsto v atTop (𝓝 0))
--       (h36 : ∀ N, v 0 = v N + ∑ k ∈ range N, p k)
--       (hχ : ∀ k, 0 ≤ χ k) (hχsum : ∀ N, ∑ k ∈ range N, χ k ≤ L 0)
--       (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2) (hL : ∀ k, L (k + 1) ≤ L k)
--       (h46 : ∀ k, L (k + 1) = α k ^ 2 * v (k + 1))
--       (hα : ∀ k, 0 ≤ α k) (hα0 : ∀ k, α k = 0 → v (k + 1) = 0)
--       (h32 : ∀ k, 0 < α k → C⁻¹ ≤ α k ^ 2)
--       (ht : ∀ d k, 0 ≤ t d k)
--       (htaylor : ∀ d k, 1 ≤ d → t d k ≤ R ^ (2 * d) * v (k + 1))
--       (hJ1 : ∀ k d, 1 ≤ d → 2 * d ≤ k + 1 → (∀ j < k, 0 < α j ∧ α j ^ 2 ≤ 3 / C) →
--         t d k ≤ (c / C) ^ d * t (2 * d) (k - d) +
--           c ^ d * R ^ (2 * d) * C * ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j)
--       (hJ2 : ∀ N, (∀ j, j + 1 < N → α j ^ 2 ≤ 3 / C) →
--         ∑ k ∈ range N, p k ≤ L 0 + 3 / C * ∑ k ∈ range (N - 1), t 1 k) :
--       C ≤ 100 * c ^ 2 * R ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Criterion`](https://prove2.me/theorems/b6210dc1-894e-490a-a262-24735151f6b5).
--
--   Supporting theorems: [`recursion`](https://prove2.me/theorems/29ed27ac-971d-48f4-ba7a-bfb704866cf8).
--
--   Previous: [`recursion`](https://prove2.me/theorems/29ed27ac-971d-48f4-ba7a-bfb704866cf8) · Next: [`norm_taylorField_sq_le`](https://prove2.me/theorems/658d541a-caf2-439c-ac49-7e33a7865643).
--
--   [Source excerpt, lines 278–294](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean#L278-L294) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean#L268-L332 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.le_of_iterate_bounds`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion

open MeasureTheory Filter Topology Finset

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.le_of_iterate_bounds_readable {C c R : ℝ} {v p χ L α : ℕ → ℝ} {t : ℕ → ℕ → ℝ}
    (hC : 0 < C) (hc : 1 ≤ c) (hR : 1 ≤ R)
    (hv : ∀ k, 0 ≤ v k) (hv0 : C⁻¹ ≤ v 0) (hvlim : Tendsto v atTop (𝓝 0))
    (h36 : ∀ N, v 0 = v N + ∑ k ∈ range N, p k)
    (hχ : ∀ k, 0 ≤ χ k) (hχsum : ∀ N, ∑ k ∈ range N, χ k ≤ L 0)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2) (hL : ∀ k, L (k + 1) ≤ L k)
    (h46 : ∀ k, L (k + 1) = α k ^ 2 * v (k + 1))
    (hα : ∀ k, 0 ≤ α k) (hα0 : ∀ k, α k = 0 → v (k + 1) = 0)
    (h32 : ∀ k, 0 < α k → C⁻¹ ≤ α k ^ 2)
    (ht : ∀ d k, 0 ≤ t d k)
    (htaylor : ∀ d k, 1 ≤ d → t d k ≤ R ^ (2 * d) * v (k + 1))
    (hJ1 : ∀ k d, 1 ≤ d → 2 * d ≤ k + 1 → (∀ j < k, 0 < α j ∧ α j ^ 2 ≤ 3 / C) →
      t d k ≤ (c / C) ^ d * t (2 * d) (k - d) +
        c ^ d * R ^ (2 * d) * C * ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j)
    (hJ2 : ∀ N, (∀ j, j + 1 < N → α j ^ 2 ≤ 3 / C) →
      ∑ k ∈ range N, p k ≤ L 0 + 3 / C * ∑ k ∈ range (N - 1), t 1 k) :
    C ≤ 100 * c ^ 2 * R ^ 2 := by sorry
