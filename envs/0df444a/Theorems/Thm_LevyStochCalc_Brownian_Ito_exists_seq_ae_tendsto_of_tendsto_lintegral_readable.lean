-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_seq_ae_tendsto_of_tendsto_lintegral_readable
-- name    : LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:12.222717+00:00
-- url     : https://prove2.me/theorems/3562f88f-3c78-4ff5-ad93-01edc45ad90f
-- title:
--   Common Almost-Everywhere Subsequence for Finite Families
-- statement:
--   Let $(\alpha,\mu)$ be a measurable measure space and let $\iota$ be a finite type. Suppose $u_i(c,\cdot)$ and $v(c,\cdot)$ are measurable real-valued functions, and for every $c\in\iota$,
--
--   $$
--   \int^\infty \|u_i(c,a)-v(c,a)\|^2\,d\mu(a)\longrightarrow0.
--   $$
--
--   Then there exists a subsequence map $m:\mathbb N\to\mathbb N$ with $i\le m(i)$ for every $i$, such that for almost every $a$, simultaneously for every $c\in\iota$,
--
--   $$
--    u_{m(i)}(c,a)\longrightarrow v(c,a).
--   $$
--
--   The squared norm is represented using `ENNReal` lower integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_seq_ae_tendsto_of_tendsto_lintegral {α : Type*} [MeasurableSpace α]
--       {μ : Measure α} {ι : Type*} [Finite ι] {u : ℕ → ι → α → ℝ} {v : ι → α → ℝ}
--       (hu : ∀ (i : ℕ) (c : ι), Measurable (u i c)) (hv : ∀ c : ι, Measurable (v c))
--       (h : ∀ c : ι, Filter.Tendsto (fun i : ℕ => ∫⁻ a, (‖u i c a - v c a‖₊ : ℝ≥0∞) ^ 2 ∂μ)
--         Filter.atTop (𝓝 0)) :
--       ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧
--         ∀ᵐ a ∂μ, ∀ c : ι, Filter.Tendsto (fun i : ℕ => u (ms i) c a) Filter.atTop (𝓝 (v c a))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Supporting theorems: [`tendsto_of_tendsto_sq_enorm`](https://prove2.me/theorems/98542836-cccb-4492-8290-6e6d19d114a0).
--
--   Previous: [`tendsto_of_tendsto_sq_enorm`](https://prove2.me/theorems/98542836-cccb-4492-8290-6e6d19d114a0) · Next: [`ae_ae_tendsto_version_clamp`](https://prove2.me/theorems/4b4b00a1-8893-4a14-9b71-7455375e4cb1).
--
--   [Source excerpt, lines 397–403](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L397-L403) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L394-L426 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`, declaration `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral_readable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} [Finite ι] {u : ℕ → ι → α → ℝ} {v : ι → α → ℝ}
    (hu : ∀ (i : ℕ) (c : ι), Measurable (u i c)) (hv : ∀ c : ι, Measurable (v c))
    (h : ∀ c : ι, Filter.Tendsto (fun i : ℕ => ∫⁻ a, (‖u i c a - v c a‖₊ : ℝ≥0∞) ^ 2 ∂μ)
      Filter.atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧
      ∀ᵐ a ∂μ, ∀ c : ι, Filter.Tendsto (fun i : ℕ => u (ms i) c a) Filter.atTop (𝓝 (v c a)) := by sorry
