-- Prove2me | Theorems.Thm_GlobalTheory_T_vectorFieldOrder_add_of_prod_strictHenselian
-- name    : GlobalTheory.T.vectorFieldOrder_add_of_prod_strictHenselian
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:01:43.521908+00:00
-- url     : https://prove2.me/theorems/f8f478aa-3aba-4703-8fe8-31efd5c1bbaa
-- title:
--   T: vector Field Order add of prod strict Henselian
-- statement:
--   The T construction uses the vector Field Order add of prod strict Henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VectorFieldOrderAddOfProdStrictHenselianStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VectorFieldOrderAddOfProdStrictHenselianStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselianStatement
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

theorem GlobalTheory.T.vectorFieldOrder_add_of_prod_strictHenselian : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (A A' : Over (Sp K)) (I I' : Type) [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (D : I → VF A) (D' : I' → VF A'), IsFrame D → IsFrame D' → ∃ D₂ : I ⊕ I' → VF (A ⊗ A'), IsFrame D₂ ∧ ∀ (M : Model R A) (N : Model R A') (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D' π n → HasOrd (M.prod N) D₂ π (m + n) := by sorry
