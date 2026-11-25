-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_exists_unif_isFnT
-- name    : GlobalTheory.ThetaFn.exists_unif_isFnT
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:26.370143+00:00
-- url     : https://prove2.me/theorems/03c10d50-2682-572d-82c5-e9d057990ffa
-- title:
--   Theta Fn: exists unif is Fn T
-- statement:
--   The Theta Fn construction uses the exists unif is Fn T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L750-L761
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L750-L761

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter

theorem GlobalTheory.ThetaFn.exists_unif_isFnT (h : ThetaUnifAV) (P : PolAV (Sp ℂ))
    (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen) :
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ ∧ u.IsRig rig ∧ ∀ n : ℕ,
        (∀ s : LB.Sec (LPow P.A P.L n (baseOver (Sp ℂ))),
          ∃! θ, u.IsThetaFn Hm χ n θ ∧ IsFnT u n s θ) ∧
        ∀ θ, u.IsThetaFn Hm χ n θ →
          ∃! s : LB.Sec (LPow P.A P.L n (baseOver (Sp ℂ))), IsFnT u n s θ := by sorry
