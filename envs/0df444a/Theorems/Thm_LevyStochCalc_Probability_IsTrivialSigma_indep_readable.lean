-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_IsTrivialSigma_indep_readable
-- name    : LevyStochCalc.Probability.IsTrivialSigma.indep_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:38.101882+00:00
-- url     : https://prove2.me/theorems/f75b0847-19ee-42e7-998a-ac50fc379cf5
-- title:
--   Independence From a Trivial Sigma-Algebra
-- statement:
--   This is an independence lemma for a null-or-conull sub-$\sigma$-algebra.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space, and let $m,m'$ be measurable spaces on $\Omega$ with $m\subseteq\mathcal F$. Assume `IsTrivialSigma P m`, meaning that every $m$-measurable set has $P$-measure either $0$ or $1$. Then $m$ and $m'$ are independent under $P$:
--
--   $$\operatorname{Indep}(m,m',P).$$
--
--   The conclusion is independent of any further relation between $m'$ and the ambient measurable space. This is a reusable technical result for discarding null-or-conull factors from independence arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsTrivialSigma.indep [IsProbabilityMeasure P] {m m' : MeasurableSpace Ω}
--       (hm : m ≤ mΩ) (h : IsTrivialSigma P m) : Indep m m' P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/TrivialSigma`](https://prove2.me/theorems/dc4060fb-e8ac-4040-ba35-772331f332f6).
--
--   Next: [`isTrivialSigma_comap_of_ae_const`](https://prove2.me/theorems/b4f6041a-5c48-4c2c-8053-7383d3a8e14f).
--
--   [Source excerpt, lines 36–37](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/TrivialSigma.lean#L36-L37) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/TrivialSigma.lean#L35-L48 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.TrivialSigma`, declaration `LevyStochCalc.Probability.IsTrivialSigma.indep`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_TrivialSigma

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/TrivialSigma.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω}

theorem LevyStochCalc.Probability.IsTrivialSigma.indep_readable [IsProbabilityMeasure P] {m m' : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (h : IsTrivialSigma P m) : Indep m m' P := by sorry
