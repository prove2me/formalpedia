-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull
-- name    : ModularCurve.XOneP.exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/29f1a919-23e8-5534-b22e-91d8d421ac37
-- title:
--   Atkin–Lehner automorphism at p exchanging the two degeneracy legs
-- statement:
--   Let $p$ be a prime, let $M$ be a nonzero natural number with $5 \le M$ and $p \nmid M$, and assume [`ModularCurve.HeckeBetaOneDefined (M * p) p`](def/ModularCurve_X1HeckeOperator.html#L84), i.e. that $y \mapsto \mathrm{qExpand}_{\mathbb Q}^{p}(y)$ (the substitution $q \mapsto q^{p}$ on Laurent series) carries the $q$-expansion function field of $X_1(Mp)$ into that of $\Gamma_1(Mp) \cap \Gamma_0(Mp\cdot p)$. Then there exist natural numbers $d, d'$, each coprime to $Mp$, an $\overline{\mathbb Q}$-algebra automorphism $\tau$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (the subfield of $\overline{\mathbb Q}$-Laurent series generated over $\overline{\mathbb Q}$ by the coefficientwise images of the $X_1(Mp)$ expansion field) and an $\overline{\mathbb Q}$-algebra automorphism $W$ of the corresponding base change of the $\Gamma_1(Mp) \cap \Gamma_0(Mp^{2})$ expansion field, such that: (i) for every $f$ in [`ModularCurve.modularFunctionFieldFull (M * p)`](def/ModularCurve_X0.html#L305) — the field generated over $\mathbb Q$ by the series $j(q^{e})$ for the nonzero divisors $e$ of $Mp$ — whose coefficientwise image lies in `x1FunctionFieldBar (M * p)`, the value of $\tau$ at that image is the coefficientwise image of `atkinLehnerInvolutionFull M p f`, the chosen automorphism swapping $j(q^{e})$ and $j(q^{ep})$ for all nonzero $e \mid M$; (ii) $W \circ \alpha = \beta \circ \langle d\rangle \circ \tau$ and (iii) $W \circ \beta = \alpha \circ \langle d'\rangle \circ \tau$ pointwise, where $\alpha$ is `heckeAlphaOneBar` (the inclusion leg), $\beta$ is `heckeBetaOneBar` (the $q \mapsto q^{p}$ leg) and $\langle\cdot\rangle$ denotes `diamondAutBar`.
--
--   This is the function-field form of the partial Atkin–Lehner involution $w_p$ at level $Mp$, together with the statement that conjugation by $w_p$ interchanges the two degeneracy legs of the Hecke correspondence $U_p$ up to diamond operators. It feeds the corresponding statement about divisors and supports on $X_1(Mp)$, used in the level-lowering analysis of $J_1(Mp)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M) [NeZero p]

    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p) :
    ∃ d d' : ℕ, d.Coprime (M * p) ∧ d'.Coprime (M * p) ∧
      ∃ (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))),

        (∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
          (hf : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) ∈ ModularCurve.x1FunctionFieldBar (M * p)),
          ((τ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
            ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((ModularCurve.atkinLehnerInvolutionFull M p f :
              ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ)) ∧

        (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)),
          W (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p x) =
            ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p
              (ModularCurve.diamondAutBar (M * p) d (τ x))) ∧

        (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)),
          W (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p x) =
            ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p
              (ModularCurve.diamondAutBar (M * p) d' (τ x))) := by sorry
