-- Prove2me | Theorems.Thm_GlobalTheory_T_glue_schemes_over_opens_along_cocycle
-- name    : GlobalTheory.T.glue_schemes_over_opens_along_cocycle
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:41:53.562114+00:00
-- url     : https://prove2.me/theorems/21792fc8-91bb-4d5a-8099-4c26daca60be
-- title:
--   T: glue schemes over opens along cocycle
-- statement:
--   The T construction uses the glue schemes over opens along cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GlueSchemesOverOpensAlongCocycleStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GlueSchemesOverOpensAlongCocycleStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GlueSchemesOverOpensAlongCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GlueSchemesOverOpensAlongCocycleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.glue_schemes_over_opens_along_cocycle : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (G : ∀ i, Over (U i).toScheme) (B : ∀ i j, Over (U i ⊓ U j).toScheme) (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i j, IsPullback (a i j) (B i j).hom (G i).hom (S.homOfLE inf_le_left)) → (∀ i j, IsPullback (b i j) (B i j).hom (G j).hom (S.homOfLE inf_le_right)) → (∀ i j k (T : Scheme.{0}) (x : T ⟶ (B i j).left) (y : T ⟶ (B j k).left) (z : T ⟶ (B i k).left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) → ∃ (A : Over S) (ψ : ∀ i, (G i).left ⟶ A.left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by sorry
