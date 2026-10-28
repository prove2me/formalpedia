-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_ae_interval_holder_readable
-- name    : LevyStochCalc.Brownian.Continuity.kc_ae_interval_holder_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:26.351971+00:00
-- url     : https://prove2.me/theorems/4c8f4cad-b521-472c-8c8e-9ef103021114
-- title:
--   Almost-Sure Local Hölder Bounds on Unit Intervals
-- statement:
--   This is the almost-sure intervalwise Hölder estimate for a Kolmogorov process. Under the probability-space, process, and `IsKolmogorovProcess` assumptions above, let $\alpha>0$ satisfy $\alpha p<q-1$. Then for $P$-almost every $\omega$, every integer $j$ admits $K\ge0$ and $N\in\mathbb N$ such that for dyadic rationals $s,t\in[j,j+1]$ with $|s-t|\le(1/2)^N$,
--
--   $$
--   |X(s,\omega)-X(t,\omega)|\le K|s-t|^\alpha.
--   $$
--
--   The constants may depend on the path and on the interval index $j$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma kc_ae_interval_holder
--       (P : Measure Ω) [IsProbabilityMeasure P]
--       (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
--       (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
--       {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
--       ∀ᵐ ω ∂P, ∀ j : ℤ, ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧
--         ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
--           (j : ℝ) ≤ s → s ≤ (j : ℝ) + 1 → (j : ℝ) ≤ t → t ≤ (j : ℝ) + 1 →
--           |s - t| ≤ (1 / 2 : ℝ) ^ N → |X s ω - X t ω| ≤ K * |s - t| ^ α
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityKolmogorovBounds`](https://prove2.me/theorems/db501a14-f954-4e21-a7e6-2ee411f6aff8).
--
--   Definition modules: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Supporting theorems: [`dyadic_holder_chaining`](https://prove2.me/theorems/749988d9-89e5-4fb5-9831-f2ad8915a549), [`kc_ae_increment_bound`](https://prove2.me/theorems/87c978a6-33c4-4d46-8fa8-81294193f4ae).
--
--   Previous: [`kc_ae_increment_bound`](https://prove2.me/theorems/87c978a6-33c4-4d46-8fa8-81294193f4ae) · Next: [`kc_ae_nbhd_holder`](https://prove2.me/theorems/61ee6149-778a-4170-b841-7de89dc30569).
--
--   [Source excerpt, lines 276–284](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L276-L284) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L271-L306 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kc_ae_interval_holder`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Continuity.kc_ae_interval_holder_readable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ j : ℤ, ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧
      ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
        (j : ℝ) ≤ s → s ≤ (j : ℝ) + 1 → (j : ℝ) ≤ t → t ≤ (j : ℝ) + 1 →
        |s - t| ≤ (1 / 2 : ℝ) ^ N → |X s ω - X t ω| ≤ K * |s - t| ^ α := by sorry
