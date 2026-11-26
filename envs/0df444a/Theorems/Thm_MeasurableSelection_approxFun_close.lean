-- Prove2me | Theorems.Thm_MeasurableSelection_approxFun_close
-- name    : MeasurableSelection.approxFun_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:21.408012+00:00
-- url     : https://prove2.me/theorems/067ac06e-ffd3-57ca-9f3b-47a87410b076
-- title:
--   Measurable Selection: approx Fun close
-- statement:
--   The Measurable Selection construction uses the approx Fun close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L174-L178
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L174-L178

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
open MeasurableSelection
variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}

theorem MeasurableSelection.approxFun_close (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) :
    (Φ a ∩ ball (approxFun hu hne hΦ n a) ((1 / 2 : ℝ) ^ n)).Nonempty := by sorry
