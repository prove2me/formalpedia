-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_kill_mul_iff
-- name    : GlobalTheory.HeckeCompare.IsAct.kill_mul_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:04.586256+00:00
-- url     : https://prove2.me/theorems/ef87e8c0-9d2c-45ab-8836-5203ba808362
-- title:
--   Is Act: kill mul iff
-- statement:
--   The Is Act construction uses the kill mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L104-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L104-L112

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

theorem GlobalTheory.HeckeCompare.IsAct.kill_mul_iff (h : IsAct ρ) (p : ℕ) (I : Ideal O) (x : Q) :
    (∀ a ∈ Ideal.span {(p : O)} * I, ρ a x = 1) ↔ ∀ a ∈ I, ρ a (x ^ p) = 1 := by sorry
