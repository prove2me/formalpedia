-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_normSq_sub_symField_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_symField_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:29.445983+00:00
-- url     : https://prove2.me/theorems/76359b53-6bf9-43ab-bb7a-bc9a40372a88
-- title:
--   Distance From Partial Symmetrization
-- statement:
--   This formalizes BKL Lemma 3.3, Equation (44), p. 12.
--
--   Let $u$ be a field with $k$ indices and let $q\le k$. Let $S_q u$ be the average over permutations of the first $q$ positions, and let $\tau_\ell$ swap positions $\ell$ and $\ell+1$. Then
--
--   $$\|u-S_qu\|^2
--   \le q^4\sum_{\substack{\ell<k\\\ell+1<q}}
--   \|u-\tau_\ell u\|^2.$$
--
--   The squared norm is the field quantity `normSq`, and the sum is over the finite set of admissible adjacent positions.
--
--   This is the combinatorial symmetrization estimate used in the approximate symmetry of Poisson iterates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem normSq_sub_symField_le {q : ℕ} (hq : q ≤ k) (u : Field ν k) :
--       normSq (u - symField q u) ≤
--         (q : ℝ) ^ 4 * ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
--           normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Permutation`](https://prove2.me/theorems/99978ac0-75f0-4e2a-93f1-fae71240d06b).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375).
--
--   Supporting theorems: [`sqrt_normSq_sub_permField_le_of_adjacent`](https://prove2.me/theorems/584de1b3-b865-446f-97d5-352cf6522404).
--
--   Previous: [`sqrt_normSq_sub_permField_le_of_adjacent`](https://prove2.me/theorems/584de1b3-b865-446f-97d5-352cf6522404).
--
--   [Source excerpt, lines 314–317](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Permutation.lean#L314-L317) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Permutation.lean#L311-L338 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Permutation`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_symField_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation

open MeasureTheory Finset
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  {ν : MeasureTheory.ProbabilityMeasure V} {k : ℕ}

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_symField_le_readable {q : ℕ} (hq : q ≤ k) (u : Field ν k) :
    normSq (u - symField q u) ≤
      (q : ℝ) ^ 4 * ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
        normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u) := by sorry
