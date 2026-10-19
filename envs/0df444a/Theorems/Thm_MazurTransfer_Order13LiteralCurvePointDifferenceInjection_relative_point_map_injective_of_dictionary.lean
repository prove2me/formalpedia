-- Prove2me | Theorems.Thm_MazurTransfer_Order13LiteralCurvePointDifferenceInjection_relative_point_map_injective_of_dictionary
-- name    : MazurTransfer.Order13LiteralCurvePointDifferenceInjection.relative_point_map_injective_of_dictionary
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:04:54.859481+00:00
-- url     : https://prove2.me/theorems/c711bdb8-d800-474c-81c4-8acdd118f4c2
-- title:
--   An actual point-difference dictionary forces injection for the literal order-thirteen curve
-- statement:
--   Let $R$ be a commutative ring and $K$ an algebraically closed field of characteristic zero with an $R$-algebra structure. Let $C_R,C_K$ be the actual order-thirteen curves, let $P$ be a relative degree-zero Picard designation over $R$, and let $a:C_R\to P$ be a morphism over $R$. Suppose a bijection $\xi:\operatorname{Pic}^0(K(C_K))\to P(K)$ identifies each actual point-difference divisor class with its image under $a$:
--   $$\xi([p-\infty^+])=a_K(p)\qquad(p\in C_K(K)),$$
--   using the actual Cartesian identification of $C_K(K)$ with $C_R(K)$. Then $a_K:C_R(K)\to P(K)$ is injective.
--
--   This transfers the positive-genus point-difference injection through a genuine divisor-class/field-point dictionary on the fixed curve. The construction of this dictionary for the represented Abel–Jacobi morphism is a separate input.
-- source:
--   Unchanged statement, local instance bodies, and target proof body from the checked MazurTheorem Order13LiteralCurvePointDifferenceInjection.lean. The Lean syntax oracles hoist the solution out of its namespace and replace imports by public constructor and theorem interfaces. The complete original type is checked with explicit anonymous-instance correspondence and proof irrelevance for the alternative proof of the same curve-integrality proposition; the public preamble is re-elaborated independently with fresh local instances. Vas and contributors, Apache-2.0; official Anthropic FLT APIs retain pin 6e837e75355538c7f80bab5b956861e86c4eacc2 and attribution. The retry adds three direct public carrier/base-interface imports and removes an unused RelPicard namespace opening after the first statement job failed; the formal statement and proof body are preserved.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the genuine point-difference dictionary on the literal
geometric field curve forces injectivity of its map to an original-base
Picard scheme. Named downstream consumer: the integral Abel-Jacobi map
and injectivity of rational curve specialization. -/
import Theorems.Thm_MazurTransfer_CurveModelPointDifferenceInjectivity_point_map_injective_of_dictionary
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_wholeCurve_isPullback
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Definitions.Def_MazurTransfer_PullbackRelativeFieldPoints
import Definitions.Def_MazurTransfer_RelativePointPostcomposition
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase





noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections
open Order13ActualCurveBaseChange CurveModelPointDifferenceInjectivity Order13ActualArithmeticCurveModel
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open ProperPointSpecializationNaturality
universe u
variable {R K : Type u} [CommRing R] [Field K] [CharZero K] [IsAlgClosed K] [Algebra R K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

variable (D : RelativePic0Designation R (curveToBase R)) (aj : SchemeHomOver (curveToBase R) D.toBase)

theorem MazurTransfer.Order13LiteralCurvePointDifferenceInjection.relative_point_map_injective_of_dictionary
    (H : ∃ pts : Pic0 K (actualCurveFunctionField K) ≃ SchemeHomOver (specMap R K) D.toBase,
      ∀ p : SchemeHomOver (𝟙 (Spec (.of K))) (curveToBase K),
        ∃ E : Divisor.degZero (K := K) (F := actualCurveFunctionField K),
          (E : Divisor K (actualCurveFunctionField K)) =
            Finsupp.single ((actualCurveModel K).pointEquivPlace p) 1 -
              Finsupp.single ((actualCurveModel K).pointEquivPlace (positiveInfinitySection K)) 1 ∧
          (pts (Pic0.mk E)).val = (p.val ≫ curveMap R K) ≫ aj.val) :
    Function.Injective (postcomp (curveToBase R) D.toBase aj.val aj.property (specMap R K))  := by sorry
