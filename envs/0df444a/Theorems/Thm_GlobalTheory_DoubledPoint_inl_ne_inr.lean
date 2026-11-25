-- Prove2me | Theorems.Thm_GlobalTheory_DoubledPoint_inl_ne_inr
-- name    : GlobalTheory.DoubledPoint.inl_ne_inr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:39.959987+00:00
-- url     : https://prove2.me/theorems/1ed4cb9e-1e97-42c5-8db9-d3a6a1f731fe
-- title:
--   Doubled Point: inl ne inr
-- statement:
--   The Doubled Point construction uses the inl ne inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CorrOfGenericOfIsSeparated.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CorrOfGenericOfIsSeparated.lean#L58-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CorrOfGenericOfIsSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory
universe u
open GlobalTheory.DoubledPoint
variable {X : Scheme.{0}} (U : X.Opens)

theorem GlobalTheory.DoubledPoint.inl_ne_inr (x : X) (hx : x ∉ U) : pushout.inl U.ι U.ι ≠ pushout.inr U.ι U.ι := by sorry
