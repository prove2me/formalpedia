-- Prove2me | Theorems.Thm_GroundTheory_Global_gaussResidue_residue_algebraMap
-- name    : GroundTheory.Global.gaussResidue_residue_algebraMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:56:01.519635+00:00
-- url     : https://prove2.me/theorems/52933658-041f-490c-bc52-49aa9d725bd1
-- title:
--   Global: gauss Residue residue algebra Map
-- statement:
--   The Global construction uses the gauss Residue residue algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L239-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L239-L243

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

theorem GroundTheory.Global.gaussResidue_residue_algebraMap (c : 𝒪) :
    gaussResidue W (residue (gaussRing W) (algebraMap 𝒪 (gaussRing W) c)) =
      algebraMap (ResidueField 𝒪) _ (residue 𝒪 c) := by sorry
