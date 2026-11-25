-- Prove2me | Theorems.Thm_GlobalTheory_SS_frobG_pow_and_closed_subgroup
-- name    : GlobalTheory.SS.frobG_pow_and_closed_subgroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:36.993795+00:00
-- url     : https://prove2.me/theorems/40f0a701-3917-4a49-8d11-c3d55c38c14e
-- title:
--   SS: frob G pow and closed subgroup
-- statement:
--   The SS construction uses the frob G pow and closed subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGPowAndClosedSubgroup.lean#L90-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGPowAndClosedSubgroup.lean#L90-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGPowAndClosedSubgroup
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
open GlobalTheory.SS.FrobSub

theorem GlobalTheory.SS.frobG_pow_and_closed_subgroup : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (F : End G) (q : ℕ), FrobG G F q → (∀ m, 1 ≤ m → FrobG G (F ^ m) (q ^ m)) ∧ ∀ (N : Over (Sp k)) [GrpObj N] (ν : N ⟶ G) (F' : End N), IsMonHom ν → IsClosedImmersion ν.left → IsMonHom (show N ⟶ N from F') → (show N ⟶ N from F') ≫ ν = ν ≫ (show G ⟶ G from F) → FrobG N F' q := by sorry
