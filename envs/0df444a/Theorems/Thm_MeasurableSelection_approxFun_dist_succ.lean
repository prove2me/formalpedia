-- Prove2me | Theorems.Thm_MeasurableSelection_approxFun_dist_succ
-- name    : MeasurableSelection.approxFun_dist_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:29.191067+00:00
-- url     : https://prove2.me/theorems/0d34d201-a661-597a-8bc4-a73fe51cbe7f
-- title:
--   Measurable Selection: approx Fun dist succ
-- statement:
--   The Measurable Selection construction uses the approx Fun dist succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L180-L191
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L180-L191

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
open MeasurableSelection
variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}

theorem MeasurableSelection.approxFun_dist_succ (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) :
    dist (approxFun hu hne hΦ n a) (approxFun hu hne hΦ (n + 1) a) ≤
      (3 / 2 : ℝ) * (1 / 2) ^ n := by sorry
