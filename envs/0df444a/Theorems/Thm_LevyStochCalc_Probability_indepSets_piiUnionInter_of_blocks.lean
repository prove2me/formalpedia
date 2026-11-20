-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_indepSets_piiUnionInter_of_blocks
-- name    : LevyStochCalc.Probability.indepSets_piiUnionInter_of_blocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:34:44.483037+00:00
-- url     : https://prove2.me/theorems/870488a4-ab38-4f03-b290-cdb04439a3a3
-- title:
--   indepSets piiUnionInter of blocks
-- statement:
--   The source theorem `LevyStochCalc.Probability.indepSets_piiUnionInter_of_blocks` is extracted from `LevyStochCalc.Probability.IndepBlocks`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Independence of two joins from blockwise independence

An independent family of σ-algebras, each containing two independent sub-σ-algebras, has the two
joins of those sub-σ-algebras independent: a finite intersection from each join is a single
intersection over the union of the two index sets, which the family's independence factors
blockwise and the blockwise independence factors again.
-/

open MeasureTheory MeasurableSpace ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω ι : Type*} [DecidableEq ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [DecidableEq ι] in

theorem _root_.LevyStochCalc.Probability.indepSets_piiUnionInter_of_blocks {m a b : ι → MeasurableSpace Ω}
    (ha : ∀ i, a i ≤ m i) (hb : ∀ i, b i ≤ m i)
    (hm : iIndep m μ) (hab : ∀ i, Indep (a i) (b i) μ) :
    IndepSets (piiUnionInter (fun i => {t | MeasurableSet[a i] t}) Set.univ)
      (piiUnionInter (fun i => {t | MeasurableSet[b i] t}) Set.univ) μ := by sorry
