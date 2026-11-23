-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_of_dvd
-- name    : GlobalTheory.HeckeCompare.IsAct.of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:53.965555+00:00
-- url     : https://prove2.me/theorems/5f721167-c5f6-4d6d-b756-0a5a42e6ff17
-- title:
--   Is Act: of dvd
-- statement:
--   The Is Act construction uses the of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L91-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeTate_IsPart_of_dvd

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

theorem GlobalTheory.HeckeCompare.IsAct.of_dvd (h : IsAct ρ) {n : ℕ} {x : Q} (hx : x ^ n = 1) {a : O} (ha : (n : O) ∣ a) : ρ a x = 1 := by sorry
