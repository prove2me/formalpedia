-- Prove2me | Theorems.Thm_GlobalTheory_TorsionDivisible_finite_torsion_and_divisible
-- name    : GlobalTheory.TorsionDivisible.finite_torsion_and_divisible
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:59:16.644824+00:00
-- url     : https://prove2.me/theorems/06a998cd-1e14-4af1-bf6a-96628784c258
-- title:
--   Torsion Divisible: finite torsion and divisible
-- statement:
--   The Torsion Divisible construction uses the finite torsion and divisible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AbelianVarietyTorsionFiniteEndomorphismDivisible.lean#L50-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AbelianVarietyTorsionFiniteEndomorphismDivisible.lean#L50-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisible
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
open GlobalTheory GlobalTheory.TorsionDivisible

theorem GlobalTheory.TorsionDivisible.finite_torsion_and_divisible :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ ∀ f : B ⟶ B, IsMonHom f → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ^ n = 1 → x ≫ f = 1) → ∃ g : B ⟶ B, IsMonHom g ∧ f = g ^ n := by sorry
