-- Prove2me | Theorems.Thm_GlobalTheory_LevelDict_ext_of_ne_zero
-- name    : GlobalTheory.LevelDict.ext_of_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:45.648219+00:00
-- url     : https://prove2.me/theorems/8140ccc1-82fa-42ce-8dc2-0c89eb17dbb6
-- title:
--   Level Dict: ext of ne zero
-- statement:
--   The Level Dict construction uses the ext of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LineBundlePowSectionsEqThetaLevel.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LineBundlePowSectionsEqThetaLevel.lean#L82-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.LevelDict

theorem GlobalTheory.LevelDict.ext_of_ne_zero {g : ℕ} {θ f f' : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (hf : Continuous f)
    (hf' : Continuous f') (h : ∀ z, θ z ≠ 0 → f z = f' z) : ∀ z, f z = f' z := by sorry
