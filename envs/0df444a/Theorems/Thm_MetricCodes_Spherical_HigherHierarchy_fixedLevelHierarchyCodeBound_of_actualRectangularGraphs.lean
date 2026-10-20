-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelHierarchyCodeBound_of_actualRectangularGraphs
-- name    : MetricCodes.Spherical.HigherHierarchy.fixedLevelHierarchyCodeBound_of_actualRectangularGraphs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/c0bc896a-848a-414e-8f04-49e678c8a9e0
-- title:
--   MetricCodes.Spherical.HigherHierarchy.fixedLevelHierarchyCodeBound_of_actualRectangularGraphs
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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherProjectionInstantiation

theorem MetricCodes.Spherical.HigherHierarchy.fixedLevelHierarchyCodeBound_of_actualRectangularGraphs
    (hboxes : ∀ {r : ℕ} {s R : ℝ}, 0 < s → s < 1 →
      ∀ (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
        Interlacing a b → 0 < a (Fin.last (r + 1)) →
          s < 2 * Gamma a b → Phi a b < R →
            ∃ (m : ℕ) (gap : ℝ) (_ : 0 < gap)
              (stable : ℕ → Prop) (_ : DecidablePred stable)
              (_ : ∀ᶠ n : ℕ in atTop, stable n)
              (G : (n : ℕ) → stable n → IndexedHierarchyGraph n),
                (∀ (n : ℕ) (h : stable n), 0 < (G n h).vertexCount) ∧
                (∀ (n : ℕ) (h : stable n), 0 < (G n h).fibreDimension) ∧
                (∀ (n : ℕ) (h : stable n) (x y : SpherePoint n),
                  (G n h).graph.correlation x y =
                    ⟪(x.val : SpherePacking.Euclidean n), y.val⟫_ℝ) ∧
                (∀ᶠ n : ℕ in atTop,
                  ∀ h : stable n,
                    s + gap < (G n h).graph.eigenvalue) ∧
                (∀ᶠ n : ℕ in atTop,
                  ∀ h : stable n,
                    (∑ i : Fin (G n h).vertexCount,
                        ((G n h).graph.dimension i : ℝ)) /
                      ((G n h).fibreDimension : ℝ) =
                      RectangularVertices.dimensionSum (m := m) a n /
                        Weyl.dimension (n - 1)
                          (Weyl.flooredWeight b n))) :
    FixedLevelHierarchyCodeBound := by sorry
