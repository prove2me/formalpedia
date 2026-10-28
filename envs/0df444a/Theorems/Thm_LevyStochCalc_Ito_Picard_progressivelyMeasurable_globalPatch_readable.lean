-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_progressivelyMeasurable_globalPatch_readable
-- name    : LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:17.335706+00:00
-- url     : https://prove2.me/theorems/d7b4eeb7-145e-4369-9114-1296769d3100
-- title:
--   Progressive Measurability Of The Global Patched Path
-- statement:
--   This is a technical measurability lemma. Let $\mathcal F$ be a filtration and let $Y_k:\mathbb R\to\Omega\to(\operatorname{Fin}(n)\to\mathbb R)$ be a countable family such that every coordinate of every $Y_k$ is progressively measurable. Then every coordinate of the glued path `globalPatch Y` is progressively measurable:
--
--   $$\forall i\in\operatorname{Fin}(n),\quad (\omega,s)\mapsto\operatorname{globalPatch}(Y,s,\omega,i)\text{ is progressively measurable}.$$
--
--   The result supports construction of a global process by selecting, below each time, one of finitely many window paths.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem progressivelyMeasurable_globalPatch
--       {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
--       (hY : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
--       (i : Fin n) :
--       Probability.ProgressivelyMeasurable ℱ fun ω s => globalPatch Y s ω i
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardGlobal`](https://prove2.me/theorems/c943d813-0c09-4024-8228-fab73533b083).
--
--   Definition modules: [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Previous: [`ae_all_eq_of_rightCont`](https://prove2.me/theorems/439cca99-ccce-4335-8a27-57cecb8617ae) · Next: [`ae_all_windows_agree`](https://prove2.me/theorems/28b35a3b-dd08-4022-854c-84cd03274ea9).
--
--   [Source excerpt, lines 102–106](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardGlobal.lean#L102-L106) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardGlobal.lean#L99-L134 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardGlobal`, declaration `LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
omit [MeasurableSpace E] [IsProbabilityMeasure P]

theorem LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch_readable
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => globalPatch Y s ω i := by sorry
