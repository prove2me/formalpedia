-- Prove2me | Theorems.Thm_GlobalTheory_LBPush_gm_eq_one
-- name    : GlobalTheory.LBPush.gm_eq_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:59:09.953823+00:00
-- url     : https://prove2.me/theorems/2892357a-ab00-45e1-9c47-5293ba6ca19a
-- title:
--   LBPush: gm eq one
-- statement:
--   The LBPush construction uses the gm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsCechDataPullbackOfLineBundleOnOpen.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsCechDataPullbackOfLineBundleOnOpen.lean#L14-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCechDataPullbackOfLineBundleOnOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.LBPush

theorem GlobalTheory.LBPush.gm_eq_one {X Z : Scheme.{0}} (κ : Z ⟶ X) [IsOpenImmersion κ] (z : Z) {U : X.Opens} (h : κ z ∈ U)
    {a : Γ(X, U)ˣ} (e : gm κ z U a = 1) : gm (𝟙 X) (κ z) U a = 1 := by sorry
