-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_effectiveEpi_morphismRestrict
-- name    : GlobalTheory.FlatDescent.effectiveEpi_morphismRestrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:55.830696+00:00
-- url     : https://prove2.me/theorems/6ac2cc58-273a-4206-b9e7-f2cd548b9348
-- title:
--   Flat Descent: effective Epi morphism Restrict
-- statement:
--   The Flat Descent construction uses the effective Epi morphism Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L117-L125

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

theorem GlobalTheory.FlatDescent.effectiveEpi_morphismRestrict (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : EffectiveEpi (p ∣_ U) := by sorry
