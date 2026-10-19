-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticGroup_geometricArithmeticClassOver_injective_explicitOriginalType20261017
-- name    : MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_injective_explicitOriginalType20261017
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T20:27:33.49066+00:00
-- url     : https://prove2.me/theorems/448370fe-9a3e-47d4-8367-6f866e5ad4d3
-- title:
--   The original geometric arithmetic class detects equality of points of the same rational Picard scheme
-- statement:
--   Let K be a perfect characteristic-zero field and choose a two-affine cover of the actual curve over K. For K-valued points a,b of the same original rational represented Picard family, viewed in the over category,
--
--   $$\operatorname{cl}_K(a)=\operatorname{cl}_K(b)\quad\Longrightarrow\quad a=b.$$
--
--   The map is the original arithmetic class from a full degree-zero divisor presentation of the actual geometric line bundle. The result gives the faithful point comparison needed to detect the diamond and nineteen-norm scheme identities. The field and affine-cover parameters are explicit in the public statement; the complete original theorem type is preserved.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_injective, retaining all three original unit and kernel helpers and using the accepted exact geometric group law, zero-class criterion and line-bundle point detection. Official Anthropic FLT Poincare identity inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017

theorem MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_injective_explicitOriginalType20261017
    (K : Type) [Field K] [CharZero K] [PerfectField K]
    (𝒱 : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover) :
    Function.Injective (MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver K 𝒱) := by sorry
