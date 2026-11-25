-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_kill_span_iff
-- name    : GlobalTheory.HeckeCompare.IsAct.kill_span_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:31.156292+00:00
-- url     : https://prove2.me/theorems/956f8229-b333-45c0-8d21-5518e0bb1a46
-- title:
--   Is Act: kill span iff
-- statement:
--   The Is Act construction uses the kill span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L114-L117

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

theorem GlobalTheory.HeckeCompare.IsAct.kill_span_iff (h : IsAct ρ) (p : ℕ) (x : Q) :
    (∀ a ∈ Ideal.span {(p : O)}, ρ a x = 1) ↔ x ^ p = 1 := by sorry
