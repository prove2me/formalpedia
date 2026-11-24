-- Prove2me | Theorems.Thm_GlobalTheory_SecLifts_mk_mem_ker_factor
-- name    : GlobalTheory.SecLifts.mk_mem_ker_factor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:52:51.115135+00:00
-- url     : https://prove2.me/theorems/946e1eb8-4a5d-4b37-951a-3d7295bbae6a
-- title:
--   Sec Lifts: mk mem ker factor
-- statement:
--   The Sec Lifts construction uses the mk mem ker factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompatibleSections.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompatibleSections.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompatibleSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SecLifts

theorem GlobalTheory.SecLifts.mk_mem_ker_factor {R : Type} [CommRing R] {I J : Ideal R} (h : I ≤ J) (x : R) :
    Ideal.Quotient.mk I x ∈ RingHom.ker (Ideal.Quotient.factor h) ↔ x ∈ J := by sorry
