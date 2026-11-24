-- Prove2me | Theorems.Thm_GlobalTheory_SS_exists_smooth_free_away
-- name    : GlobalTheory.SS.exists_smooth_free_away
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:39.814687+00:00
-- url     : https://prove2.me/theorems/1cc90de8-99ce-43b5-b626-5814f940029e
-- title:
--   SS: exists smooth free away
-- statement:
--   The SS construction uses the exists smooth free away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothFreeAway.lean#L42-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothFreeAway.lean#L42-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAway
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

theorem GlobalTheory.SS.exists_smooth_free_away : ∀ (k C : Type) [Field k] [PerfectField k] [CommRing C] [Nontrivial C] [IsReduced C] [Algebra k C] [Algebra.FiniteType k C] (M : Type) [AddCommGroup M] [Module C M] [Module.Finite C M], ∃ f : C, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by sorry
