-- Prove2me | Theorems.Thm_GlobalTheory_TorusAlg_snd_pull_eq_zero
-- name    : GlobalTheory.TorusAlg.snd_pull_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:27.159966+00:00
-- url     : https://prove2.me/theorems/e786a6fb-e600-55da-800e-2107dae2ebdd
-- title:
--   Torus Alg: snd pull eq zero
-- statement:
--   The Torus Alg construction uses the snd pull eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/ThetaLevelCharacters/MemThetaLevelCharDimZero.lean#L156-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/ThetaLevelCharacters/MemThetaLevelCharDimZero.lean#L156-L169

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
open Out Out.Inh

theorem GlobalTheory.TorusAlg.snd_pull_eq_zero (φ : Sp (DualNumber ℂ) ⟶ Sp ℂ) (hφ : φ = spMap (algebraMap ℂ (DualNumber ℂ)))
    (U : (Sp ℂ).Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (f : Γ(Sp ℂ, U)) :
    TrivSqZeroExt.snd (show DualNumber ℂ from
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((φ.appLE U ⊤ h).hom f)) = 0 := by sorry
