-- Prove2me | Theorems.Thm_OAI_SingleLatticeCovering_single_lattice_covering
-- name    : OAI.SingleLatticeCovering.single_lattice_covering
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:22.644544+00:00
-- url     : https://prove2.me/theorems/b170607c-c467-437e-a129-843dc720d838
-- statement:
--   The theorem states that there is a positive absolute constant C such that for every dimension n ≥ 2 and every convex body K in ℝⁿ (here a convex body means a compact convex set with nonempty interior), there exists a lattice L, namely a ℤ-submodule of ℝⁿ that carries the discrete topology and is a full-rank ℤ-lattice spanning ℝⁿ over ℝ, such that translates of K by lattice points cover the whole space, i.e. the Minkowski sum K + L equals all of ℝⁿ, and the covering density is bounded: the Lebesgue volume of K (taken as a real number) divided by the covolume of L is at most C · n · log n. The theorem is stated as admitted, with its proof left as sorry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SingleLatticeCovering.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SingleLatticeCovering.lean; bytes 476..837
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SingleLatticeCovering

namespace OAI

namespace SingleLatticeCovering

open MeasureTheory

open scoped Pointwise

theorem single_lattice_covering :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n →
      ∀ (K : Set (Space n)), IsConvexBody K →
        ∃ (L : Submodule ℤ (Space n)) (_ : DiscreteTopology L),
          IsZLattice ℝ L ∧ LatticeCovers K L ∧
            (volume K).toReal / ZLattice.covolume L ≤ C * (n : ℝ) * Real.log (n : ℝ) := by sorry

end SingleLatticeCovering
end OAI
