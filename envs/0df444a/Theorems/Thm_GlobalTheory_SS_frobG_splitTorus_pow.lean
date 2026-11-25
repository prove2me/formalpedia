-- Prove2me | Theorems.Thm_GlobalTheory_SS_frobG_splitTorus_pow
-- name    : GlobalTheory.SS.frobG_splitTorus_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:54.217696+00:00
-- url     : https://prove2.me/theorems/c2cd00cd-a2b8-5c79-b3a7-8142f1ced8af
-- title:
--   SS: frob G split Torus pow
-- statement:
--   The SS construction uses the frob G split Torus pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGSplitTorusPow.lean#L36-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FrobGSplitTorusPow.lean#L36-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGSplitTorusPow
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
open GlobalTheory GlobalTheory.SS

theorem GlobalTheory.SS.frobG_splitTorus_pow :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : End (splitTorus (Sp k) X)) (q : ℕ), FrobG (splitTorus (Sp k) X) F q → ∃ m, 1 ≤ m ∧ ∀ l, (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from F ^ (m * l)) = (𝟙 (splitTorus (Sp k) X)) ^ (q ^ (m * l)) := by sorry
