-- Prove2me | Theorems.Thm_GlobalTheory_LevQuot_exists_geomPoint
-- name    : GlobalTheory.LevQuot.exists_geomPoint
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:06.791557+00:00
-- url     : https://prove2.me/theorems/93583f97-8f5f-437b-9f15-0e8ebf3231bc
-- title:
--   Lev Quot: exists geom Point
-- statement:
--   The Lev Quot construction uses the exists geom Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L28-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}

theorem GlobalTheory.LevQuot.exists_geomPoint (Z : Scheme.{0}) (z : Z) : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k)
    (w : Spec (CommRingCat.of k) ⟶ Z) (p : Spec (CommRingCat.of k)), w p = z := by sorry
