-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankActualProjectedAxisCompletion_fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
-- name    : MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion.fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:09.321996+00:00
-- url     : https://prove2.me/theorems/5b4f96fb-da6d-49f4-8a8b-afe2ae8f7a6d
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion.fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxProjectedAxisWitness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange
open MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency

theorem MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion.fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
    (hrecurrence : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n + 1 →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing (n + 1)
          (RectangularVertices.signature a (n + 1) v)
          (flooredCoordinates b (n + 1))) →
      ∀ (low high : BoxIndex (r + 1) m)
        (row : Fin (r + 2))
        (_ : boxSignature (m := m) a (n + 1) high =
          raiseWeight (boxSignature (m := m) a (n + 1) low) row),
        CanonicalBoxAdjacentFischerRecurrence a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i)
          low high row) :
    FixedLevelHierarchyCodeBound := by sorry
