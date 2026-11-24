-- Prove2me | Theorems.Thm_GlobalTheory_SS_LinCore_core
-- name    : GlobalTheory.SS.LinCore.core
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:26.667376+00:00
-- url     : https://prove2.me/theorems/9b765737-9c30-418f-882f-e33604aeddb5
-- title:
--   Lin Core: core
-- statement:
--   The Lin Core construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankLeOfWeightsUnipotentSymplectic.lean#L201-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinrankLeOfWeightsUnipotentSymplectic.lean#L201-L304

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

theorem GlobalTheory.SS.LinCore.core [FiniteDimensional 𝕜 V] (B : LinearMap.BilinForm 𝕜 V) (hB : B.Nondegenerate)
    (T Φ Ψ : Module.End 𝕜 V) (q : ℕ) (hq : 2 ≤ q) (hT : IsNilpotent T) (hΨ : Φ * Ψ = 1)
    (hΦ : ∀ x y, B (Φ x) (Φ y) = q * B x y) (h : Φ * (T + 1) = (T + 1) ^ q * Φ)
    (W : Submodule 𝕜 V) (P : ℚ[X]) (hP : ∀ β : ℂ, aeval β P = 0 → ‖β‖ < q)
    (hW : ∀ x ∈ W, Φ x = (q : 𝕜) • x) (hPW : ∀ x, T x = 0 → aeval Φ P x ∈ W) :
    Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker T) + Module.finrank 𝕜 W := by sorry
