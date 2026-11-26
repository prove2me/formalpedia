-- Prove2me | Theorems.Thm_MeasurableSelection_approx_succ_spec
-- name    : MeasurableSelection.approx_succ_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:21.656739+00:00
-- url     : https://prove2.me/theorems/c7ffdf6b-14cc-5301-bf1d-8bb782d81b9e
-- title:
--   Measurable Selection: approx succ spec
-- statement:
--   Successive stages of the scheme select points close both to `Φ a` and to the
--   previous stage.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L160-L165
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L160-L165

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
open MeasurableSelection
variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}

theorem MeasurableSelection.approx_succ_spec (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) :
    (Φ a ∩ (ball (u ((approx hu hne hΦ (n + 1)).1 a)) ((1 / 2 : ℝ) ^ (n + 1)) ∩
      ball (u ((approx hu hne hΦ n).1 a)) ((1 / 2 : ℝ) ^ n))).Nonempty := by sorry
