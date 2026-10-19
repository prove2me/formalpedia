-- Prove2me | Theorems.Thm_MazurTransfer_Order13SixMarkedSectionsDistinct_six_sections_field_precomposition_injective
-- name    : MazurTransfer.Order13SixMarkedSectionsDistinct.six_sections_field_precomposition_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:41:16.677011+00:00
-- url     : https://prove2.me/theorems/200c9cf7-27c1-4618-919d-0a991d12fed1
-- title:
--   Six actual marked sections remain distinct over every field point
-- statement:
--   Let $R$ be a commutative ring in which two is a unit, let $k$ be a field, and let $s:\operatorname{Spec}k\to\operatorname{Spec}R$ be any morphism. For the actual sections $$\sigma_0,\ldots,\sigma_5=\infty^+,\infty^-,(0,1),(0,-1),(-1,1),(-1,-1)$$ of the actual order-thirteen curve, the six composites $\sigma_i\circ s$ are pairwise distinct. This supplies the distinctness hypothesis for the genus-two six-section Picard chart criterion. No algebraic-closedness assumption on $k$ is needed.
-- source:
--   Unchanged statement and proof bodies from MazurTheorem Order13SixMarkedSectionsDistinct.lean and Order13MarkedSectionPointSeparation.lean. The original chart-overlap proof is retained through eleven selected declarations from Order13IntegralCurveProperViaHyperellipticMap.lean, together with the unchanged range formulation. Complete Lean frontend ranges select the declarations and hoist namespace, import, and universe commands. The proof uses the public actual six-section constructors and public infinity-coordinate evaluations. The complete original closed kernel type is compared with the solution. Per-file headers and Apache-2.0 attribution are retained. Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_Order13SixMarkedIntegralSections
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve MazurTransfer.Order13IntegralSections
universe u

theorem MazurTransfer.Order13SixMarkedSectionsDistinct.six_sections_field_precomposition_injective (R : Type u) [CommRing R]  (h2 : IsUnit (2 : R))
    (k : Type u) [Field k] (s : Spec (.of k) ⟶ Spec (.of R)) :
    Function.Injective (fun i : Fin 6 => s ≫ (sixMarkedSections R i).val)  := by sorry
