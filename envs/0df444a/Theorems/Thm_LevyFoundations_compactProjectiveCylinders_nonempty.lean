-- Prove2me | Theorems.Thm_LevyFoundations_compactProjectiveCylinders_nonempty
-- name    : LevyFoundations.compactProjectiveCylinders_nonempty
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:57:14.427194+00:00
-- url     : https://prove2.me/theorems/5423e99e-c469-4950-ba15-426587cb13a9
-- title:
--   Nonempty compatible compact cylinders over increasing finite coordinate sets
-- statement:
--   Given increasing finite coordinate sets and a nonempty nested family of compact closed finite-dimensional sets, with every higher-level point restricting into every lower-level set, a global product point belongs to each cylinder. The proof is extracted from the compact-product/Cantor step in LeanLevy's original Kolmogorov extension proof.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/Processes/Kolmogorov.lean, source proof of ProjectiveFamily.content_tendsto_zero, compact product/Cantor and coordinate reconstruction section around lines 200–352.

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.Topology.MetricSpace.Polish

open MeasureTheory Set Finset Filter
open scoped ENNReal Topology

theorem LevyFoundations.compactProjectiveCylinders_nonempty
    {ι : Type*} {α : ι → Type*}
    [∀ i, TopologicalSpace (α i)] [∀ i, PolishSpace (α i)]
    (hne : ∀ i, Nonempty (α i))
    (J : ℕ → Finset ι) (hJ_mono : Monotone J)
    (L : ∀ n, Set (∀ j : J n, α j))
    (hL_closed : ∀ n, IsClosed (L n))
    (hL_compact : ∀ n, IsCompact (L n))
    (hL_nonempty : ∀ n, (L n).Nonempty)
    (hL_restrict : ∀ {n m} (hnm : n ≤ m) (x : ∀ j : J m, α j),
      x ∈ L m → Finset.restrict₂ (hJ_mono hnm) x ∈ L n) :
    (⋂ n, cylinder (J n) (L n)).Nonempty := by sorry
