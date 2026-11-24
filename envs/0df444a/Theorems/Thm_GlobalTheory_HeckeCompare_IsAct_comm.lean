-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_comm
-- name    : GlobalTheory.HeckeCompare.IsAct.comm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:33.858811+00:00
-- url     : https://prove2.me/theorems/60599425-d109-4b33-9039-342f24fad25d
-- title:
--   Is Act: comm
-- statement:
--   The Is Act construction uses the comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L95-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L95-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {O Q : Type} [CommRing O] [CommGroup Q] {ρ : O → Q →* Q}

theorem GlobalTheory.HeckeCompare.IsAct.comm (h : IsAct ρ) (a b : O) (x : Q) : ρ a (ρ b x) = ρ b (ρ a x) := by sorry
