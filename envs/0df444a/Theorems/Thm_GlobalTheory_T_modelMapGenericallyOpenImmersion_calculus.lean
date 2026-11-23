-- Prove2me | Theorems.Thm_GlobalTheory_T_modelMapGenericallyOpenImmersion_calculus
-- name    : GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:13.596848+00:00
-- url     : https://prove2.me/theorems/451c0949-27b3-4d27-99a4-0f9329000198
-- title:
--   T: model Map Generically Open Immersion calculus
-- statement:
--   The T construction uses the model Map Generically Open Immersion calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ModelMapGenericallyOpenImmersionCalculusStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ModelMapGenericallyOpenImmersionCalculusStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → (∀ (A : Over (Sp K)) (M N : Model R A), M.Irr → M.Le N → GenIso M N (𝟙 A)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A'') (f : A ⟶ A') (g : A' ⟶ A''), N.Irr → GenIso M N f → GenIso N P g → GenIso M P (f ≫ g)) ∧ (∀ (A A' : Over (Sp K)) (M : Model R A) (N : Model R A') (f : A ≅ A'), (GenIso M N f.hom → GenIso N M f.inv) ∧ (GenIso M N f.hom ↔ GenIso (M.twist f) N (𝟙 A')) ∧ (M.Irr → (M.twist f).Irr)) ∧ (∀ (A A' B B' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R B) (Q : Model R B') (f : A ⟶ B) (g : A' ⟶ B'), GenIso M P f → GenIso N Q g → GenIso (M.prod N) (P.prod Q) (f ⊗ₘ g)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A''), M.Irr → N.Irr → P.Irr → GenIso ((M.prod N).prod P) (M.prod (N.prod P)) (α_ A A' A'').hom ∧ GenIso (M.prod N) (N.prod M) (β_ A A').hom) := by sorry
