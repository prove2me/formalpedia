-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_map_ip
-- name    : GlobalTheory.GramCount.map_ip
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:18.152328+00:00
-- url     : https://prove2.me/theorems/d9a84e9c-b3b9-4969-adab-dfeb8bb1c469
-- title:
--   Gram Count: map ip
-- statement:
--   The Gram Count construction uses the map ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L65-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}

theorem GlobalTheory.GramCount.map_ip {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) (x y : Fin n → A) :
    φ (ip c x y) = ip c' (fun i => φ (x i)) (fun i => φ (y i)) := by sorry
