-- Prove2me | Theorems.Thm_GlobalTheory_TorusAlg_thetaChar_level
-- name    : GlobalTheory.TorusAlg.thetaChar_level
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:16:24.448533+00:00
-- url     : https://prove2.me/theorems/af59f2c7-f64d-4343-ad4d-d5fe2e982faa
-- title:
--   Torus Alg: theta Char level
-- statement:
--   The Torus Alg construction uses the theta Char level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/ThetaLevelCharacters/MemThetaLevelCharDimZero.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/ThetaLevelCharacters/MemThetaLevelCharDimZero.lean#L55-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusAlg
open ReciprocityTheory.PTheta
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}

theorem GlobalTheory.TorusAlg.thetaChar_level (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2)
    (hb : ∀ i, b i = 0 ∨ b i = 1 / 2) :
    thetaChar τ a b ≠ 0 ∧
    thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ = Submodule.span ℂ {thetaChar τ a b} ∧
    ∀ n : ℕ, 0 < n → Module.finrank ℂ (thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) n τ) = n ^ g := by sorry
