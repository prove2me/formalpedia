-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_sqrt_normSq_sub_permField_le_of_adjacent_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_le_of_adjacent_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:20.63901+00:00
-- url     : https://prove2.me/theorems/584de1b3-b865-446f-97d5-352cf6522404
-- title:
--   Permutation Displacement From Adjacent Displacements
-- statement:
--   Let $u$ be a field with $k$ index positions and let $q\le k$. Suppose $B\ge0$ and every adjacent transposition of positions $\ell$ and $\ell+1$ with $\ell+1<q$ moves $u$ by at most $B$ in Hilbert–Schmidt norm:
--
--   $$\sqrt{\|u-\tau_\ell u\|^2}\le B.$$
--
--   Then every permutation $\sigma$ that fixes all positions outside the first $q$ positions satisfies
--
--   $$\sqrt{\|u-\sigma u\|^2}\le q^2B.$$
--
--   The result is purely combinatorial and applies to arbitrary fields of $L^2$ classes; it does not use properties of the measure.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sqrt_normSq_sub_permField_le_of_adjacent {q : ℕ} (hq : q ≤ k) (u : Field ν k) {B : ℝ}
--       (hB0 : 0 ≤ B)
--       (hB : ∀ ℓ : Fin k, ℓ.val + 1 < q →
--         √(normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤ B)
--       {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ fixingOutside (slots k 0 q)) :
--       √(normSq (u - permField σ u)) ≤ (q : ℝ) ^ 2 * B
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Permutation`](https://prove2.me/theorems/99978ac0-75f0-4e2a-93f1-fae71240d06b).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Next: [`normSq_sub_symField_le`](https://prove2.me/theorems/76359b53-6bf9-43ab-bb7a-bc9a40372a88).
--
--   [Source excerpt, lines 223–228](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Permutation.lean#L223-L228) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Permutation.lean#L220-L270 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Permutation`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_le_of_adjacent`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation

open FunctionalInequalities.Analysis.Tensor
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  {ν : MeasureTheory.ProbabilityMeasure V} {k : ℕ}

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_le_of_adjacent_readable {q : ℕ} (hq : q ≤ k) (u : Field ν k) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ ℓ : Fin k, ℓ.val + 1 < q →
      √(normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤ B)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ fixingOutside (slots k 0 q)) :
    √(normSq (u - permField σ u)) ≤ (q : ℝ) ^ 2 * B := by sorry
