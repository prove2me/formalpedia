-- Prove2me | Theorems.Thm_GroundTheory_Global_gaussResidue_residue
-- name    : GroundTheory.Global.gaussResidue_residue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:17.374752+00:00
-- url     : https://prove2.me/theorems/2e4dbc1e-3255-4df9-9f06-99e14dc8955c
-- title:
--   Global: gauss Residue residue
-- statement:
--   The Global construction uses the gauss Residue residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L227-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L227-L237

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
noncomputable section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)

theorem GroundTheory.Global.gaussResidue_residue (a : W.toAffine.CoordinateRing) :
    gaussResidue W (residue (gaussRing W) (algebraMap _ (gaussRing W) a)) =
      algebraMap _ _ (coordReduce W a) := by sorry
