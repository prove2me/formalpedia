-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_IsTrivialSigma_indep_408915f
-- name    : LevyStochCalc.Probability.IsTrivialSigma.indep_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:06:00.418193+00:00
-- url     : https://prove2.me/theorems/bdcd57e2-c181-4cf1-bd9b-ffa72d149e4a
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
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/TrivialSigma.lean#L35-L48 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.TrivialSigma`, declaration `LevyStochCalc.Probability.IsTrivialSigma.indep`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/TrivialSigma.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem LevyStochCalc.Probability.IsTrivialSigma.indep_408915f [IsProbabilityMeasure P] {m m' : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (h : IsTrivialSigma P m) : Indep m m' P := by sorry
