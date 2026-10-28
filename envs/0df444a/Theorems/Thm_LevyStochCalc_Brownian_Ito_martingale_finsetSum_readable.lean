-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_finsetSum_readable
-- name    : LevyStochCalc.Brownian.Ito.martingale_finsetSum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:48.260089+00:00
-- url     : https://prove2.me/theorems/fba98d15-9105-40a1-9195-5076f35b1f94
-- title:
--   Finite Sums of Martingales
-- statement:
--   This vendored theorem states that finite sums preserve the martingale property.
--
--   Let $s$ be a finite set of indices, let $f_i(t,\omega)$ be a real-valued process for each index $i$, and suppose that every $f_i$ with $i\in s$ is a martingale with respect to the filtration $\mathcal F$ and measure $P$. Then the process
--
--   $$
--   (t,\omega)\longmapsto\sum_{i\in s}f_i(t,\omega)
--   $$
--
--   is also a martingale with respect to $\mathcal F$ and $P$.
--
--   The result is a basic closure property used when assembling finite-dimensional stochastic processes.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem martingale_finsetSum {ι : Type*} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
--       (s : Finset ι) (f : ι → ℝ → Ω → ℝ)
--       (hf : ∀ i ∈ s, MeasureTheory.Martingale (f i) ℱ P) :
--       MeasureTheory.Martingale (fun t ω => ∑ i ∈ s, f i t ω) ℱ P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoVersionSup`](https://prove2.me/theorems/eac19afb-1a3e-420c-b0c9-4e8c576afefc).
--
--   Next: [`lintegral_iSup_sq_norm_version_sub_le`](https://prove2.me/theorems/3d71b361-cb18-4a6b-a812-4786fccd9817).
--
--   [Source excerpt, lines 78–81](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionSup.lean#L78-L81) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionSup.lean#L77-L97 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoVersionSup`, declaration `LevyStochCalc.Brownian.Ito.martingale_finsetSum`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionSup

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionSup.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
universe u
variable {Ω : Type u}
variable [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}

theorem LevyStochCalc.Brownian.Ito.martingale_finsetSum_readable {ι : Type*} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (s : Finset ι) (f : ι → ℝ → Ω → ℝ)
    (hf : ∀ i ∈ s, MeasureTheory.Martingale (f i) ℱ P) :
    MeasureTheory.Martingale (fun t ω => ∑ i ∈ s, f i t ω) ℱ P := by sorry
