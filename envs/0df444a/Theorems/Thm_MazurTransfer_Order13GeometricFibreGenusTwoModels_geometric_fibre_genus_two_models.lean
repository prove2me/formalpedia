-- Prove2me | Theorems.Thm_MazurTransfer_Order13GeometricFibreGenusTwoModels_geometric_fibre_genus_two_models
-- name    : MazurTransfer.Order13GeometricFibreGenusTwoModels.geometric_fibre_genus_two_models
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:32:11.880976+00:00
-- url     : https://prove2.me/theorems/b5a5af4b-9899-4cd2-a8e0-2a3508f2a74c
-- title:
--   Actual order-thirteen geometric fibres carry genus-two Riemann–Roch models
-- statement:
--   Let $R$ be a commutative ring in which $104$ is a unit, let $k$ be an algebraically closed field, and let $s:\operatorname{Spec}k\to\operatorname{Spec}R$ be any geometric point. For the actual order-thirteen curve $c_R:C_R\to\operatorname{Spec}R$, there exist a function field $L/k$, a curve model $M$ of $L$, and an isomorphism $$M.C\;\xrightarrow{\sim}\;C_R\times_{\operatorname{Spec}R}\operatorname{Spec}k$$ compatible with the structure morphisms. Moreover, some divisor $K_c$ on $L/k$ satisfies $$\ell(D)-\ell(K_c-D)=\deg(D)+1-2\qquad\text{for every divisor }D.$$ This supplies the actual geometric-fibre model needed by the six-section Picard chart criterion.
-- source:
--   Unchanged statement and target proof body from checked MazurTheorem Order13GeometricFibreGenusTwoModels.lean, with its unchanged internal actual_genus_two_riemannRoch proof from Order13ActualGenusTwoCurveModel.lean. Direct public interfaces provide the literal actual CurveModel, function-field invariants and actual Cartesian base-change square. Full original and public types are compared by closed kernel witnesses, and the statement preamble is checked independently. Official Anthropic FLT APIs retain Apache-2.0 attribution and exact commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Vas and contributors, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Definitions.Def_MazurTransfer_Order13ActualCurveBaseChangeMap
import Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_wholeCurve_isPullback
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualArithmeticCurveModel MazurTransfer.Order13ActualCurveBaseChange

theorem MazurTransfer.Order13GeometricFibreGenusTwoModels.geometric_fibre_genus_two_models (R : Type u) [CommRing R]  (h104 : IsUnit (104 : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (s : Spec (.of k) ⟶ Spec (.of R)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L)
      (M : CurveModel k L) (e : M.C ≅ pullback (curveToBase R) s)
      (he : e.hom ≫ pullback.snd (curveToBase R) s = M.toBase)
      (Kc : Divisor k L),
      ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - 2  := by sorry
