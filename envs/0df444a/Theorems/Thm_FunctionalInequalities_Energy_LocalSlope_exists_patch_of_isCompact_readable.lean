-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_exists_patch_of_isCompact_readable
-- name    : FunctionalInequalities.Energy.LocalSlope.exists_patch_of_isCompact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:59.024809+00:00
-- url     : https://prove2.me/theorems/ea72d420-aff6-4dac-9243-2603cf6d9d59
-- title:
--   Globally Lipschitz Patch From Finitely Many Compact Cores
-- statement:
--   This theorem constructs a global Lipschitz patch from finitely many disjoint compact cores.
--
--   Let $V$ be a normed additive group, let $f:V\to\mathbb R$ be globally $L$-Lipschitz, let $\alpha\ge0$, and let $N\in\mathbb N$. Let $K_n\subseteq V$ and $c_n\ge0$ satisfy
--
--   1. every $K_n$ is compact;
--   2. distinct $K_i,K_j$ are disjoint;
--   3. $f$ is $c_n$-Lipschitz on $K_n$;
--   4. $c_n\le L+\alpha$ for every $n$.
--
--   Then there exists $F:V\to\mathbb R$ such that
--
--   $$
--   \operatorname{LipschitzWith}(9L+8\alpha,F),
--   $$
--
--   and
--
--   $$
--   |F(x)-f(x)|\le 2L+2\alpha\quad\text{for every }x,
--   $$
--
--   while, for every $n<N$ and $x\in K_n$,
--
--   $$
--   F(x)=f(x),
--   \qquad
--   \operatorname{AsymptoticLipschitz.apply}(F,x)\le c_n.
--   $$
--
--   The declaration is `exists_patch_of_isCompact_readable`. The constants $L$, $\alpha$, and $c_n$ are nonnegative-real parameters represented by `NNReal`; the pointwise asymptotic-Lipschitz bound is an `ENNReal` inequality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.LocalSlope`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_patch_of_isCompact {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0}
--       (N : ℕ) (Kc : ℕ → Set V) (c : ℕ → ℝ≥0) (hcomp : ∀ n, IsCompact (Kc n))
--       (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j))
--       (hlipK : ∀ n, LipschitzOnWith (c n) f (Kc n)) (hcle : ∀ n, c n ≤ L + α) :
--       ∃ F : V → ℝ, LipschitzWith (9 * L + 8 * α) F ∧
--         (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
--         (∀ n < N, ∀ x ∈ Kc n, F x = f x) ∧
--         (∀ n < N, ∀ x ∈ Kc n, AsymptoticLipschitz.apply F x ≤ (c n : ℝ≥0∞))
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Density`](https://prove2.me/theorems/5367291c-d0c5-48f5-b722-92a892987587).
--
--   Definition modules: [`Energy/LocalSlope/Relaxation`](https://prove2.me/theorems/5763c613-ee60-472a-abfb-a2d2d79c15c8).
--
--   Supporting theorems: [`exists_thickening_pairwise_disjoint`](https://prove2.me/theorems/b2a5cca9-524f-466c-8c07-05aff010b370).
--
--   Previous: [`exists_thickening_pairwise_disjoint`](https://prove2.me/theorems/b2a5cca9-524f-466c-8c07-05aff010b370) · Next: [`exists_partition`](https://prove2.me/theorems/b31b55c4-8b5a-467c-9181-e00d16b2a28b).
--
--   [Source excerpt, lines 171–178](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L171-L178) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L166-L548 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.LocalSlope.exists_patch_of_isCompact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density

open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
omit [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Energy.LocalSlope.exists_patch_of_isCompact_readable {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0}
    (N : ℕ) (Kc : ℕ → Set V) (c : ℕ → ℝ≥0) (hcomp : ∀ n, IsCompact (Kc n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j))
    (hlipK : ∀ n, LipschitzOnWith (c n) f (Kc n)) (hcle : ∀ n, c n ≤ L + α) :
    ∃ F : V → ℝ, LipschitzWith (9 * L + 8 * α) F ∧
      (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
      (∀ n < N, ∀ x ∈ Kc n, F x = f x) ∧
      (∀ n < N, ∀ x ∈ Kc n, AsymptoticLipschitz.apply F x ≤ (c n : ℝ≥0∞)) := by sorry
