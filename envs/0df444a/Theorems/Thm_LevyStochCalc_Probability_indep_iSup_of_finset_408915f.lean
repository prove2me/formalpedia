-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_indep_iSup_of_finset_408915f
-- name    : LevyStochCalc.Probability.indep_iSup_of_finset_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:05:59.386479+00:00
-- url     : https://prove2.me/theorems/a838183e-6f3d-497e-87b3-3c28b4b423b2
-- title:
--   Independence Of A Countable Sigma-Algebra Supremum
-- statement:
--   Let $(\Omega,P)$ be a probability space, let $m_i$ be a family of sigma-algebras indexed by $\iota$, and let $m'$ be another sigma-algebra. Assume $m_i\leq m_\Omega$ for every $i$ and $m'\leq m_\Omega$. If for every finite set $S\subseteq\iota$,
--
--   $$\bigvee_{i\in S}m_i\ \text{ is independent of }m',$$
--
--   then
--
--   $$\bigvee_{i\in\iota}m_i\ \text{ is independent of }m'.$$
--
--   This is a general independence-extension lemma from finite subjoins to the full supremum.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/IndepJoin.lean#L87-L102 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.IndepJoin`, declaration `LevyStochCalc.Probability.indep_iSup_of_finset`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/IndepJoin.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*} {m₁ m₂ m₃ mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem LevyStochCalc.Probability.indep_iSup_of_finset_408915f {ι : Type*} {m : ι → MeasurableSpace Ω} {m' : MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ mΩ) (h_le' : m' ≤ mΩ)
    (h : ∀ S : Finset ι, Indep (⨆ i ∈ S, m i) m' P) :
    Indep (⨆ i, m i) m' P := by sorry
