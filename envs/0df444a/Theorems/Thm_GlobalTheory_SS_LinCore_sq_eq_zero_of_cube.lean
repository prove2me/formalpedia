-- Prove2me | Theorems.Thm_GlobalTheory_SS_LinCore_sq_eq_zero_of_cube
-- name    : GlobalTheory.SS.LinCore.sq_eq_zero_of_cube
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:42.1887+00:00
-- url     : https://prove2.me/theorems/c1a57eef-3514-4bd4-adc9-c31632bbf00b
-- title:
--   Lin Core: sq eq zero of cube
-- statement:
--   The Lin Core construction uses the sq eq zero of cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankLeOfWeightsUnipotentSymplectic.lean#L169-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankLeOfWeightsUnipotentSymplectic.lean#L169-L183

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplectic
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LinCore
open Polynomial
variable {𝕜 V : Type} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Module ℚ V] [IsScalarTower ℚ 𝕜 V]
omit [CharZero 𝕜] [Module ℚ V] [IsScalarTower ℚ 𝕜 V]

theorem GlobalTheory.SS.LinCore.sq_eq_zero_of_cube (T : Module.End 𝕜 V) (hT : IsNilpotent T)
    (h32 : ∀ x, (T ^ (2 + 1)) x = 0 → (T ^ 2) x = 0) (x : V) : T (T x) = 0 := by sorry
