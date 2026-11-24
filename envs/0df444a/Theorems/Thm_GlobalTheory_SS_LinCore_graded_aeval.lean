-- Prove2me | Theorems.Thm_GlobalTheory_SS_LinCore_graded_aeval
-- name    : GlobalTheory.SS.LinCore.graded_aeval
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:36:05.594906+00:00
-- url     : https://prove2.me/theorems/97ca1286-07be-45bf-828b-cef0882af2f6
-- title:
--   Lin Core: graded aeval
-- statement:
--   The Lin Core construction uses the graded aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankLeOfWeightsUnipotentSymplectic.lean#L156-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankLeOfWeightsUnipotentSymplectic.lean#L156-L166

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

theorem GlobalTheory.SS.LinCore.graded_aeval (T Φ : Module.End 𝕜 V) (q : ℕ) (hq : q ≠ 0) (hT : IsNilpotent T)
    (h : Φ * (T + 1) = (T + 1) ^ q * Φ) (i : ℕ) (c : ℚ) (p : ℚ[X]) (x : V)
    (hx : (T ^ (i + 1)) x = 0) :
    aeval (c • Φ) p ((T ^ i) x) = (T ^ i) (aeval ((c * (q : ℚ) ^ i) • Φ) p x) := by sorry
