-- Prove2me | Theorems.Thm_GlobalTheory_KeyPow_value_at_normalForm
-- name    : GlobalTheory.KeyPow.value_at_normalForm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:45.564451+00:00
-- url     : https://prove2.me/theorems/de877bbe-eba9-4a2b-84a5-a7a58f945297
-- title:
--   Key Pow: value at normal Form
-- statement:
--   The Key Pow construction uses the value at normal Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ValueAtNormalForm.lean#L47-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ValueAtNormalForm.lean#L47-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ValueAtNormalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow

theorem GlobalTheory.KeyPow.value_at_normalForm :
    ∀ (N : ℕ → ℕ) (g₀ : ℕ) (κ : KeyIn ℂ → ℂˣ) (g : ℕ) (a b : Fin g → ℂ), g₀ ≤ g → GlobalTheory.KeyPow.ClauseH ℂ N g₀ κ → (∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 → κ x = 1) → ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ), c ≠ 0 → M.det ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c → (κ x : ℂ) = (M.det ^ 4 / c ^ 8) ^ N g := by sorry
