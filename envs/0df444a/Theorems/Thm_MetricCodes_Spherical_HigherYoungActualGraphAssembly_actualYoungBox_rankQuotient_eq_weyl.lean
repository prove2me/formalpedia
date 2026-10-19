-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungActualGraphAssembly_actualYoungBox_rankQuotient_eq_weyl
-- name    : MetricCodes.Spherical.HigherYoungActualGraphAssembly.actualYoungBox_rankQuotient_eq_weyl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/1a1a97e2-9829-4490-a1be-c4eaaaffaa7a
-- title:
--   MetricCodes.Spherical.HigherYoungActualGraphAssembly.actualYoungBox_rankQuotient_eq_weyl
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
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungGraphAssembly
open MetricCodes.Spherical.HigherYoungMovingFibres
open MetricCodes.Spherical.HigherProjectionInstantiation

theorem MetricCodes.Spherical.HigherYoungActualGraphAssembly.actualYoungBox_rankQuotient_eq_weyl
    {r m n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (G : RealizedHilbertGraph (BoxIndex (r + 1) m) (SpherePoint n) E
      (YoungAmbient n (boxSignature (m := m) a n))
      (YoungCoordinateAmbient n (boxSignature (m := m) a n)))
    (hdimension : ∀ i : BoxIndex (r + 1) m,
      G.dimension i = Module.finrank ℝ
        (YoungVertex (n := n) (boxSignature (m := m) a n) i))
    (hweyl : ∀ i : BoxIndex (r + 1) m,
      MetricCodes.Spherical.HigherHierarchy.Weyl.dimension n
        (boxSignature (m := m) a n i) =
        (Module.finrank ℝ
          (YoungVertex (n := n) (boxSignature (m := m) a n) i) : ℝ))
    (hfibre :
      MetricCodes.Spherical.HigherHierarchy.Weyl.dimension (n - 1)
        (MetricCodes.Spherical.HigherHierarchy.Weyl.flooredWeight b
          n) = (Module.finrank ℝ E : ℝ)) :
    ((∑ i : Fin
        (actualYoungIndexedHierarchyGraph
          (boxSignature (m := m) a n) G).vertexCount,
      ((actualYoungIndexedHierarchyGraph
        (boxSignature (m := m) a n) G).graph.dimension i : ℝ)) /
      ((actualYoungIndexedHierarchyGraph
        (boxSignature (m := m) a n) G).fibreDimension : ℝ)) =
      MetricCodes.Spherical.HigherHierarchy.RectangularVertices.dimensionSum
        (m := m) a n /
        MetricCodes.Spherical.HigherHierarchy.Weyl.dimension (n - 1)
          (MetricCodes.Spherical.HigherHierarchy.Weyl.flooredWeight b
            n) := by sorry
