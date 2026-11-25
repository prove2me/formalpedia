-- Prove2me | Theorems.Thm_GlobalTheory_SS_exists_frobG_baseChange
-- name    : GlobalTheory.SS.exists_frobG_baseChange
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:46.334831+00:00
-- url     : https://prove2.me/theorems/cacbb9c3-2c97-41a3-bed4-1dae620bedd1
-- title:
--   SS: exists frob G base Change
-- statement:
--   The SS construction uses the exists frob G base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L318-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L318-L336

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
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
noncomputable section
open GlobalTheory GlobalTheory.SS
open FrobField

theorem GlobalTheory.SS.exists_frobG_baseChange : ∀ (W k : Type) [CommRing W] [Field k] (ρ : W →+* k) (p r : ℕ) [Fact p.Prime] [CharP k p], 1 ≤ r → (∀ w, ρ w ^ (p ^ r) = ρ w) → (∀ c : k, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∃ F : End ((Over.pullback (spMap ρ)).obj G), FrobG _ F (p ^ r) ∧ ∀ (x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback (spMap ρ)).obj G) (τ : k →+* k), (∀ c, τ c = c ^ (p ^ r)) → (x ≫ (show (Over.pullback (spMap ρ)).obj G ⟶ (Over.pullback (spMap ρ)).obj G from F)).left ≫ pullback.fst G.hom (spMap ρ) = spMap τ ≫ x.left ≫ pullback.fst G.hom (spMap ρ) := by sorry
