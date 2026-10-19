-- Prove2me | Theorems.Thm_MazurTransfer_CurveModelPointDifferenceInjectivity_point_map_injective_of_dictionary
-- name    : MazurTransfer.CurveModelPointDifferenceInjectivity.point_map_injective_of_dictionary
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T01:46:44.841798+00:00
-- url     : https://prove2.me/theorems/21d5fa1a-4f8f-4c91-9af4-de4801b33850
-- title:
--   A genuine point-difference Picard dictionary makes a curve point map injective
-- statement:
--   Let $K$ be algebraically closed, let $F/K$ be an essentially finite-type one-variable function field with constant field $K$ and positive genus, and let $M$ be a smooth proper model. Fix a point $s\in M(K)$, a set $S$, a bijection $e:\operatorname{Pic}^0(F/K)\to S$, and a map $j:M(K)\to S$. Suppose that for every point $p$, the value $j(p)$ is $e([p-s])$, witnessed by the actual degree-zero point-difference divisor on the model. Then
--   $$j\text{ is injective}.$$
--
--   The divisor dictionary is an explicit hypothesis, not an assumed identification of unrelated point sets. The theorem transfers the rational-place Abel–Jacobi injection to any point map supplied with that dictionary. Its named downstream use is the actual integral order-thirteen Abel–Jacobi morphism.
-- source:
--   Original checked MazurTheorem bridge: CurveModelPointDifferenceInjectivity.lean, lines24–45, SHA256 67885b2e34444f3c01c551eca06acda189a34ace2a89b945d710333cdf7faa8f. Public prerequisite: rational-place Picard injection83b0fa97-7bc7-423f-a786-a793767eee16. Underlying curve-model/place interfaces originate in Apache-2.0 Anthropic FLT at6e837e75355538c7f80bab5b956861e86c4eacc2.

import Mathlib
import Definitions.Def_MazurTransfer_CurveModelPointDifference
import Definitions.Def_MazurTransfer_RationalPlacePicardPointClass
import Theorems.Thm_MazurTransfer_RationalPlacePicardInjection_pointClass_injective
open CategoryTheory AlgebraicGeometry AlgebraicCurve MazurTransfer
open MazurTransfer.CurveModelPointDifferenceInjectivity
universe u v z

theorem MazurTransfer.CurveModelPointDifferenceInjectivity.point_map_injective_of_dictionary {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (M : CurveModel K F) (hC : ConstantsAreBase K F)
    (hgen : 0 < genusFF K F) {S : Type z} (pts : Pic0 K F ≃ S)
    (j : ModelPoint M → S) (s : ModelPoint M)
    (h : ∀ p, ∃ E : Divisor.degZero (K := K) (F := F),
      (E : Divisor K F) = Finsupp.single (M.pointEquivPlace p) 1 -
        Finsupp.single (M.pointEquivPlace s) 1 ∧ pts (Pic0.mk E) = j p) :
    Function.Injective j := by sorry
