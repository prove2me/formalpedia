-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_indep_sup_left_of_indep_408915f
-- name    : LevyStochCalc.Probability.indep_sup_left_of_indep_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:05:59.168058+00:00
-- url     : https://prove2.me/theorems/9f95c4cc-ab33-4659-8ff6-2c0b54dff21b
-- title:
--   Independence After Joining the Left Sigma-Algebras
-- statement:
--   This is a sigma-algebra join lemma for independence.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space and let $m_1,m_2,m_3\subseteq\mathcal F$ be measurable spaces. Assume:
--
--   1. $m_1\perp m_3$ under $P$.
--   2. $m_2\perp(m_1\vee m_3)$ under $P$.
--
--   Then the join of the first two sigma-algebras is independent of the third:
--
--   $$m_1\vee m_2\perp m_3.$$
--
--   This technical result packages the product-measure calculation needed to iterate independence along an ordered family of sigma-algebras.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/IndepJoin.lean#L47-L62 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.IndepJoin`, declaration `LevyStochCalc.Probability.indep_sup_left_of_indep`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Probability.indep_sup_left_of_indep_408915f (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) (h₃ : m₃ ≤ mΩ)
    (h13 : Indep m₁ m₃ P) (h2 : Indep m₂ (m₁ ⊔ m₃) P) : Indep (m₁ ⊔ m₂) m₃ P := by sorry
