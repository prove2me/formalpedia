-- Prove2me | Theorems.Thm_LevyFoundations_compactProjectiveThinning_nonempty
-- name    : LevyFoundations.compactProjectiveThinning_nonempty
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:58:03.613314+00:00
-- url     : https://prove2.me/theorems/b8b7e6f2-8537-4611-827b-55b2b87069d7
-- title:
--   Positive lower mass survives summable compact thinning of projective cylinders
-- statement:
--   A consistent probability-measure family with positive lower mass on nested finite-dimensional sets admits nonempty intersections of geometrically accurate compact approximants at every finite level. Extracted from LeanLevy's original Kolmogorov content-continuity proof.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/Processes/Kolmogorov.lean, original compact thinning and geometric-deficit argument around lines 108–200.

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory Set Finset Filter
open scoped ENNReal Topology

theorem LevyFoundations.compactProjectiveThinning_nonempty
    {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]
    [∀ i, TopologicalSpace (α i)]
    [∀ i, PolishSpace (α i)]
    [∀ i, BorelSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    (J : ℕ → Finset ι) (hJ_mono : Monotone J)
    (T : ∀ n, Set (∀ j : J n, α j))
    (mT : ∀ n, MeasurableSet (T n))
    (hT_anti : ∀ {n m} (hnm : n ≤ m),
      T m ⊆ Finset.restrict₂ (hJ_mono hnm) ⁻¹' T n)
    (K : ∀ n, Set (∀ j : J n, α j))
    (hK_compact : ∀ n, IsCompact (K n))
    (ε : ℝ≥0∞) (hε_pos : 0 < ε) (hε_ne_top : ε ≠ ⊤)
    (h_lower : ∀ n, ε ≤ pf.measure (J n) (T n))
    (hK_diff : ∀ n, pf.measure (J n) (T n \ K n) ≤ ε / 2 ^ (n + 2)) :
    ∀ n, (K n ∩ ⋂ k : Fin n,
      Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' K k).Nonempty := by sorry
