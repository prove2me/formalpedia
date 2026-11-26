-- Prove2me | Theorems.Thm_MeasurableSelection_exists_measurable_selection
-- name    : MeasurableSelection.exists_measurable_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:25:43.887617+00:00
-- url     : https://prove2.me/theorems/2594e93d-3e24-4c3c-8644-b37bba4ddf67
-- title:
--   Measurable Selection: exists measurable selection
-- statement:
--   **The Kuratowski–Ryll-Nardzewski measurable selection theorem** (Kechris,
--   *Classical Descriptive Set Theory*, Theorem 12.13; Srivastava, *A Course on Borel Sets*,
--   Theorem 5.2.1).
--
--   Let `α` be an arbitrary measurable space and `Y` a Polish space, presented as a complete
--   separable metric space carrying its Borel σ-algebra.  Let `Φ : α → Set Y` have nonempty
--   closed values and be weakly measurable, i.e. `{a | Φ a ∩ U ≠ ∅}` is measurable for every
--   open `U ⊆ Y`.  Then `Φ` has a Borel-measurable selection: there exists a measurable
--   `f : α → Y` with `f a ∈ Φ a` for every `a`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/Solution.lean#L59-L65
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/Solution.lean#L59-L65

import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_Solution
import Theorems.Thm_exists_measurable_selection

set_option autoImplicit false
open TopologicalSpace
open MeasurableSelection

theorem MeasurableSelection.exists_measurable_selection {α : Type*} [MeasurableSpace α] {Y : Type*}
    [MetricSpace Y] [SeparableSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {Φ : α → Set Y} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a := by sorry
