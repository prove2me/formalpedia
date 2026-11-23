-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_appTop_morphismRestrict_apply
-- name    : GlobalTheory.FlatDescent.appTop_morphismRestrict_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:40.902547+00:00
-- url     : https://prove2.me/theorems/9aba94c1-1e2d-471f-950e-79df3e9a904d
-- title:
--   Flat Descent: app Top morphism Restrict apply
-- statement:
--   The Flat Descent construction uses the app Top morphism Restrict apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L113-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}

theorem GlobalTheory.FlatDescent.appTop_morphismRestrict_apply (p : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    (p ∣_ U).appTop (U.topIso.inv a) = (p ⁻¹ᵁ U).topIso.inv (p.app U a) := by sorry
