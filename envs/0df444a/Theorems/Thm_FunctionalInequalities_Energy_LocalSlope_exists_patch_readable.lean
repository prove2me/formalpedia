-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_exists_patch_readable
-- name    : FunctionalInequalities.Energy.LocalSlope.exists_patch_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:55.00273+00:00
-- url     : https://prove2.me/theorems/8a654b9d-4f28-40fc-a4e5-430f38247dc3
-- title:
--   Large-Measurable-Set Lipschitz Patch
-- statement:
--   This theorem produces a globally Lipschitz approximation agreeing with a globally Lipschitz function on most of a probability space.
--
--   Let $V$ be a finite-dimensional real inner-product normed space with its Borel measurable structure, let $\nu$ be a probability measure on $V$, and let $f:V\to\mathbb R$ be globally $L$-Lipschitz. Let $\alpha>0$ be represented by `NNReal`, and let $\delta>0$ be an `ENNReal` value. Then there exist a function $F:V\to\mathbb R$ and a measurable set $K\subseteq V$ such that
--
--   1. $F$ is globally $(9L+8\alpha)$-Lipschitz;
--   2. $\nu(K^c)\le\delta$;
--   3. $F=f$ on $K$;
--   4. for every $x\in V$,
--      $$
--      |F(x)-f(x)|\le 2L+2\alpha;
--      $$
--   5. for every $x\in K$,
--      $$
--      \operatorname{AsymptoticLipschitz.apply}(F,x)
--      \le \operatorname{apply}(f,x)+2\alpha.
--      $$
--
--   The declaration is `exists_patch_readable`. The measure bound and slope comparison use $[0,\infty]$ values (`ENNReal`), and the conclusion is existential for each strictly positive $\alpha$ and $\delta$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.LocalSlope`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_patch (ν : ProbabilityMeasure V) {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
--       {α : ℝ≥0} (hα : 0 < α) {δ : ℝ≥0∞} (hδ : 0 < δ) :
--       ∃ (F : V → ℝ) (K : Set V), LipschitzWith (9 * L + 8 * α) F ∧ MeasurableSet K ∧
--         (ν : Measure V) Kᶜ ≤ δ ∧ (∀ x ∈ K, F x = f x) ∧
--         (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
--         ∀ x ∈ K, AsymptoticLipschitz.apply F x ≤ apply f x + 2 * (α : ℝ≥0∞)
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Density`](https://prove2.me/theorems/5367291c-d0c5-48f5-b722-92a892987587).
--
--   Definition modules: [`Energy/LocalSlope/Basic`](https://prove2.me/theorems/403376af-90fc-4aef-aed0-aefc10593586), [`Energy/LocalSlope/Relaxation`](https://prove2.me/theorems/5763c613-ee60-472a-abfb-a2d2d79c15c8).
--
--   Supporting theorems: [`exists_partition`](https://prove2.me/theorems/b31b55c4-8b5a-467c-9181-e00d16b2a28b), [`exists_patch_of_isCompact`](https://prove2.me/theorems/ea72d420-aff6-4dac-9243-2603cf6d9d59).
--
--   Previous: [`exists_partition`](https://prove2.me/theorems/b31b55c4-8b5a-467c-9181-e00d16b2a28b) · Next: [`relaxation_le_localSlope_of_lipschitzWith`](https://prove2.me/theorems/56be8628-41c6-4a74-81ac-de10156e3c1f).
--
--   [Source excerpt, lines 685–690](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L685-L690) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L681-L753 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.LocalSlope.exists_patch`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [CompleteSpace V]

theorem FunctionalInequalities.Energy.LocalSlope.exists_patch_readable (ν : ProbabilityMeasure V) {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {α : ℝ≥0} (hα : 0 < α) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ (F : V → ℝ) (K : Set V), LipschitzWith (9 * L + 8 * α) F ∧ MeasurableSet K ∧
      (ν : Measure V) Kᶜ ≤ δ ∧ (∀ x ∈ K, F x = f x) ∧
      (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
      ∀ x ∈ K, AsymptoticLipschitz.apply F x ≤ apply f x + 2 * (α : ℝ≥0∞) := by sorry
