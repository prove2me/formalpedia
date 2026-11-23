-- Prove2me | Theorems.Thm_GlobalTheory_Tw_commute_of_commute_separable
-- name    : GlobalTheory.Tw.commute_of_commute_separable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:10.043121+00:00
-- url     : https://prove2.me/theorems/077e0cfb-b541-4990-8d62-2d68e1f4a905
-- title:
--   Tw: commute of commute separable
-- statement:
--   The Tw construction uses the commute of commute separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L382-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L382-L406

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw

theorem GlobalTheory.Tw.commute_of_commute_separable {n : ℕ} {A g h : Matrix (Fin n) (Fin n) ℂ} (hA : A.charpoly.Separable)
    (hg : Commute A g) (hh : Commute A h) : Commute g h := by sorry
