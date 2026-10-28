-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_level_bad_measure_readable
-- name    : LevyStochCalc.Brownian.Continuity.kc_level_bad_measure_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:23.969575+00:00
-- url     : https://prove2.me/theorems/0aab2f8f-d712-4737-86f0-b7eebb793739
-- title:
--   Dyadic-Level Bad-Set Measure Bound
-- statement:
--   This is the per-level bad-set estimate for a Kolmogorov process. Let $(\Omega,P)$ be a probability space, $X:\mathbb R\to\Omega\to\mathbb R$, $p,q\in\mathbb R$, $M\in\mathbb R_{\ge0}$, and assume `hX : IsKolmogorovProcess X P p q M`. For every $\alpha\in\mathbb R$ and $n\in\mathbb N$, the union over $k<2^n$ of the events
--
--   $$
--   \left\{\omega:\bigl((1/2)^\alpha\bigr)^n<\left|X\!\left(\frac{k+1}{2^n},\omega\right)-X\!\left(\frac{k}{2^n},\omega\right)\right|\right\}
--   $$
--
--   has measure at most
--
--   $$
--   \operatorname{ofReal}\!\left(M\bigl((1/2)^{q-\alpha p-1}\bigr)^n\right).
--   $$
--
--   The conclusion is an `ENNReal` inequality and does not assume $\alpha p<q-1$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma kc_level_bad_measure
--       (P : Measure Ω) [IsProbabilityMeasure P]
--       (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
--       (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
--       {α : ℝ} (n : ℕ) :
--       P (⋃ k ∈ Finset.range (2 ^ n),
--           {ω | ((1 / 2 : ℝ) ^ α) ^ n
--               < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|})
--         ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityKolmogorovBounds`](https://prove2.me/theorems/db501a14-f954-4e21-a7e6-2ee411f6aff8).
--
--   Supporting theorems: [`kc_exponent_identity`](https://prove2.me/theorems/015b3d90-70b0-4878-af84-3becbce9c7eb), [`kolmogorov_markov_bound`](https://prove2.me/theorems/cc3bbae1-93c7-4b2a-a726-18938f9d796c).
--
--   Previous: [`kolmogorov_markov_bound`](https://prove2.me/theorems/cc3bbae1-93c7-4b2a-a726-18938f9d796c) · Next: [`exists_tendsto_of_local_holder`](https://prove2.me/theorems/46c83da3-bc37-4fcf-a556-d68a3d13e420).
--
--   [Source excerpt, lines 98–106](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L98-L106) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L94-L143 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kc_level_bad_measure`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.kc_level_bad_measure_readable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (n : ℕ) :
    P (⋃ k ∈ Finset.range (2 ^ n),
        {ω | ((1 / 2 : ℝ) ^ α) ^ n
            < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|})
      ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n) := by sorry
