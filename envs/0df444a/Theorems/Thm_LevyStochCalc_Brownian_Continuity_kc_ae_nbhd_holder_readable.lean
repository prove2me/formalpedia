-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_ae_nbhd_holder_readable
-- name    : LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:35.105003+00:00
-- url     : https://prove2.me/theorems/61ee6149-778a-4170-b841-7de89dc30569
-- title:
--   Almost-Sure Neighborhood Hölder Bounds
-- statement:
--   This is the almost-sure local Hölder estimate on dyadic rationals. Let $(\Omega,P)$, $X$, $p,q,M$, and `hX` be as above, and assume $\alpha>0$ and $\alpha p<q-1$. Then for $P$-almost every $\omega$ and every $t\in\mathbb R$, there exist $K\ge0$ and $\rho>0$ such that whenever dyadic rationals $s,s'$ lie in $(t-\rho,t+\rho)$,
--
--   $$
--   |X(s,\omega)-X(s',\omega)|\le K|s-s'|^\alpha.
--   $$
--
--   This is the local regularity hypothesis used to extend dyadic paths continuously.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma kc_ae_nbhd_holder
--       (P : Measure Ω) [IsProbabilityMeasure P]
--       (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
--       (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
--       {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
--       ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ dyadicRationals,
--         ∀ s' ∈ dyadicRationals, s ∈ Set.Ioo (t - ρ) (t + ρ) →
--           s' ∈ Set.Ioo (t - ρ) (t + ρ) → |X s ω - X s' ω| ≤ K * |s - s'| ^ α
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityKolmogorovBounds`](https://prove2.me/theorems/db501a14-f954-4e21-a7e6-2ee411f6aff8).
--
--   Definition modules: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Supporting theorems: [`kc_ae_interval_holder`](https://prove2.me/theorems/4c8f4cad-b521-472c-8c8e-9ef103021114).
--
--   Previous: [`kc_ae_interval_holder`](https://prove2.me/theorems/4c8f4cad-b521-472c-8c8e-9ef103021114) · Next: [`kolmogorov_modification_ae_eq`](https://prove2.me/theorems/82073c74-a718-40a3-bc28-fdee99fa3cee).
--
--   [Source excerpt, lines 313–320](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L313-L320) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L308-L402 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder_readable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ dyadicRationals,
      ∀ s' ∈ dyadicRationals, s ∈ Set.Ioo (t - ρ) (t + ρ) →
        s' ∈ Set.Ioo (t - ρ) (t + ρ) → |X s ω - X s' ω| ≤ K * |s - s'| ^ α := by sorry
