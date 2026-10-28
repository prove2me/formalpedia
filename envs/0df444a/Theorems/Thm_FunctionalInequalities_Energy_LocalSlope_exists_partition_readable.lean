-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_exists_partition_readable
-- name    : FunctionalInequalities.Energy.LocalSlope.exists_partition_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:53.411985+00:00
-- url     : https://prove2.me/theorems/b31b55c4-8b5a-467c-9181-e00d16b2a28b
-- title:
--   Measurable Partition By Local-Slope Bands
-- statement:
--   This theorem constructs a measurable partition adapted to the local slope of a globally Lipschitz function.
--
--   Let $V$ be a second-countable Borel measurable normed additive group, let $f:V\to\mathbb R$ be globally $L$-Lipschitz with $L\in[0,\infty)$, and let $\alpha>0$ be represented by `NNReal`. Then there exist sets $D_i\subseteq V$ and constants $c_i\in[0,\infty)$, indexed by $i\in\mathbb N$, such that
--
--   1. every $D_i$ is measurable;
--   2. the sets $D_i$ are pairwise disjoint and cover $V$;
--   3. $c_i\le L+\alpha$ for every $i$;
--   4. $f$ is $c_i$-Lipschitz on $D_i$;
--   5. for every $x\in D_i$,
--      $$
--      c_i\le \operatorname{apply}(f,x)+\alpha.
--      $$
--
--   The Lean declaration is `exists_partition_readable`. The local slope and the final comparison are expressed in `ENNReal`, while $L$, $\alpha$, and $c_i$ are nonnegative real constants represented by `NNReal`. This is a technical partition lemma used in patching arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.LocalSlope`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_partition {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0} (hα : 0 < α) :
--       ∃ (D : ℕ → Set V) (c : ℕ → ℝ≥0),
--         (∀ i, MeasurableSet (D i)) ∧ Pairwise (Function.onFun Disjoint D) ∧
--         (⋃ i, D i) = Set.univ ∧ (∀ i, c i ≤ L + α) ∧
--         (∀ i, LipschitzOnWith (c i) f (D i)) ∧
--         (∀ i, ∀ x ∈ D i, ((c i : ℝ≥0∞)) ≤ apply f x + (α : ℝ≥0∞))
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Density`](https://prove2.me/theorems/5367291c-d0c5-48f5-b722-92a892987587).
--
--   Definition modules: [`Energy/LocalSlope/Basic`](https://prove2.me/theorems/403376af-90fc-4aef-aed0-aefc10593586).
--
--   Supporting theorems: [`lowerSemicontinuous_secant`](https://prove2.me/theorems/fd7d5e26-5f7d-4c26-af0b-4d2fd37844d8).
--
--   Previous: [`exists_patch_of_isCompact`](https://prove2.me/theorems/ea72d420-aff6-4dac-9243-2603cf6d9d59) · Next: [`exists_patch`](https://prove2.me/theorems/8a654b9d-4f28-40fc-a4e5-430f38247dc3).
--
--   [Source excerpt, lines 567–572](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L567-L572) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L563-L679 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.LocalSlope.exists_partition`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density

open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Energy.LocalSlope.exists_partition_readable {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0} (hα : 0 < α) :
    ∃ (D : ℕ → Set V) (c : ℕ → ℝ≥0),
      (∀ i, MeasurableSet (D i)) ∧ Pairwise (Function.onFun Disjoint D) ∧
      (⋃ i, D i) = Set.univ ∧ (∀ i, c i ≤ L + α) ∧
      (∀ i, LipschitzOnWith (c i) f (D i)) ∧
      (∀ i, ∀ x ∈ D i, ((c i : ℝ≥0∞)) ≤ apply f x + (α : ℝ≥0∞)) := by sorry
