-- Prove2me | Theorems.Thm_GlobalTheory_FrameFibre_herm_of_trace
-- name    : GlobalTheory.FrameFibre.herm_of_trace
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:54.027417+00:00
-- url     : https://prove2.me/theorems/365b9214-0ed0-4a95-be71-c5e89ba3828d
-- title:
--   Frame Fibre: herm of trace
-- statement:
--   The Frame Fibre construction uses the herm of trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLevelBlockOfEq.lean#L90-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLevelBlockOfEq.lean#L90-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FrameFibre
variable {E : Type} [Field E] [NumberField E] {r : ℕ}
variable [IsCMField E]

theorem GlobalTheory.FrameFibre.herm_of_trace {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hspan : Submodule.span E (Set.range φ) = ⊤) (G A : Matrix (Fin r) (Fin r) E) (ξ : E) (hξ : ξ ≠ 0)
    (h : ∀ v w, Algebra.trace ℚ E (ξ * FD.herm G (A *ᵥ φ v) (A *ᵥ φ w)) =
      Algebra.trace ℚ E (ξ * FD.herm G (φ v) (φ w))) (x y : Fin r → E) :
    FD.herm G (A *ᵥ x) (A *ᵥ y) = FD.herm G x y := by sorry
