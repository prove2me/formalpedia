-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_recursion_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.recursion_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:31.583426+00:00
-- url     : https://prove2.me/theorems/29ed27ac-971d-48f4-ba7a-bfb704866cf8
-- title:
--   Dyadic Recursion Estimate
-- statement:
--   This technical lemma establishes the recursion used in the operator-route criterion.
--
--   Let $C,c,R\in\mathbb R$ and let $v,\chi,L,\alpha:\mathbb N\to\mathbb R$ and $t:\mathbb N\to\mathbb N\to\mathbb R$. Assume:
--
--   1. $C>0$, $c\ge1$, $R\ge1$, and $d\ge1$.
--   2. $v_{k+1}\le(121/100)C^{-1}$ and $\chi_k\ge0$ for every $k$.
--   3. Every partial sum of $\chi$ is at most $L_0$, and $L_0\le( (11/10)C^{-1})^2$.
--   4. Whenever $j+1<N$, $0<\alpha_j$ and $\alpha_j^2\le3/C$.
--   5. $t_{d,k}\ge0$, $t_{d,k}\le R^{2d}v_{k+1}$, and, whenever $2d\le k+1$ and the preceding scale bounds hold,
--      $$t_{d,k}\le(c/C)^d t_{2d,k-d}+c^dR^{2d}C\sum_{j\in[(k+1-2d),k)}\chi_j.$$
--
--   Then
--
--   $$\sum_{k<N-d}t_{d,k}\le(c/C)^d\sum_{k<N-2d}t_{2d,k}+5d\,c^dC^{-1}R^{2d}.$$
--
--   This is a neutral auxiliary estimate that packages the finite-index decomposition into the indices where the Taylor recursion applies and the at most $2d$ remaining indices.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem recursion {C c R : ℝ} {v χ L α : ℕ → ℝ} {t : ℕ → ℕ → ℝ} {N d : ℕ}
--       (hC : 0 < C) (hc : 1 ≤ c) (hR : 1 ≤ R) (hd : 1 ≤ d)
--       (hvk : ∀ k, v (k + 1) ≤ 121 / 100 * C⁻¹)
--       (hχ : ∀ k, 0 ≤ χ k) (hχsum : ∀ N, ∑ k ∈ range N, χ k ≤ L 0)
--       (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2)
--       (hαN : ∀ j, j + 1 < N → 0 < α j ∧ α j ^ 2 ≤ 3 / C)
--       (ht : ∀ d k, 0 ≤ t d k)
--       (htaylor : ∀ d k, 1 ≤ d → t d k ≤ R ^ (2 * d) * v (k + 1))
--       (hJ1 : ∀ k d, 1 ≤ d → 2 * d ≤ k + 1 → (∀ j < k, 0 < α j ∧ α j ^ 2 ≤ 3 / C) →
--         t d k ≤ (c / C) ^ d * t (2 * d) (k - d) +
--           c ^ d * R ^ (2 * d) * C * ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j) :
--       ∑ k ∈ range (N - d), t d k ≤
--         (c / C) ^ d * ∑ k ∈ range (N - 2 * d), t (2 * d) k +
--           5 * d * c ^ d * C⁻¹ * R ^ (2 * d)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Criterion`](https://prove2.me/theorems/b6210dc1-894e-490a-a262-24735151f6b5).
--
--   Next: [`le_of_iterate_bounds`](https://prove2.me/theorems/f80538b2-5d61-41ae-9ced-cdc9bb4e7bf2).
--
--   [Source excerpt, lines 151–164](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean#L151-L164) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean#L147-L232 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion`, declaration `_private.FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion.0.FunctionalInequalities.KLS.LogConcave.PoissonIterate.recursion`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion

open MeasureTheory Filter Topology Finset

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.recursion_readable {C c R : ℝ} {v χ L α : ℕ → ℝ} {t : ℕ → ℕ → ℝ} {N d : ℕ}
    (hC : 0 < C) (hc : 1 ≤ c) (hR : 1 ≤ R) (hd : 1 ≤ d)
    (hvk : ∀ k, v (k + 1) ≤ 121 / 100 * C⁻¹)
    (hχ : ∀ k, 0 ≤ χ k) (hχsum : ∀ N, ∑ k ∈ range N, χ k ≤ L 0)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2)
    (hαN : ∀ j, j + 1 < N → 0 < α j ∧ α j ^ 2 ≤ 3 / C)
    (ht : ∀ d k, 0 ≤ t d k)
    (htaylor : ∀ d k, 1 ≤ d → t d k ≤ R ^ (2 * d) * v (k + 1))
    (hJ1 : ∀ k d, 1 ≤ d → 2 * d ≤ k + 1 → (∀ j < k, 0 < α j ∧ α j ^ 2 ≤ 3 / C) →
      t d k ≤ (c / C) ^ d * t (2 * d) (k - d) +
        c ^ d * R ^ (2 * d) * C * ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j) :
    ∑ k ∈ range (N - d), t d k ≤
      (c / C) ^ d * ∑ k ∈ range (N - 2 * d), t (2 * d) k +
        5 * d * c ^ d * C⁻¹ * R ^ (2 * d) := by sorry
