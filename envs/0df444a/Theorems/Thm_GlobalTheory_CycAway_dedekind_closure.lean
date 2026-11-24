-- Prove2me | Theorems.Thm_GlobalTheory_CycAway_dedekind_closure
-- name    : GlobalTheory.CycAway.dedekind_closure
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:11.201833+00:00
-- url     : https://prove2.me/theorems/04ae7e7a-6574-45c0-9555-9b633b825d7e
-- title:
--   Cyc Away: dedekind closure
-- statement:
--   The Cyc Away construction uses the dedekind closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsLocalizationOfLeClosure.lean#L64-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsLocalizationOfLeClosure.lean#L64-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsLocalizationOfLeClosure
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
open GlobalTheory GlobalTheory.CycAway
open NumberField

theorem GlobalTheory.CycAway.dedekind_closure {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n a : ℕ} (hn : n.Prime)
    [IsCyclotomicExtension {n ^ a} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ (n ^ a)) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) ∧ Algebra.FiniteType ℤ (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by sorry
