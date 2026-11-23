-- Prove2me | Theorems.Thm_GlobalTheory_SS_LinCore_eq_zero_of_isCoprime
-- name    : GlobalTheory.SS.LinCore.eq_zero_of_isCoprime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:49.031303+00:00
-- url     : https://prove2.me/theorems/d379444d-36de-47c2-b79e-fc461d9600c6
-- title:
--   Lin Core: eq zero of is Coprime
-- statement:
--   The Lin Core construction uses the eq zero of is Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankLeOfWeightsUnipotentSymplectic.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankLeOfWeightsUnipotentSymplectic.lean#L19-L23

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

theorem GlobalTheory.SS.LinCore.eq_zero_of_isCoprime (f : Module.End 𝕜 V) {a b : ℚ[X]} (h : IsCoprime a b) {y : V}
    (ha : aeval f a y = 0) (hb : aeval f b y = 0) : y = 0 := by sorry
