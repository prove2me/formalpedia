-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_eq_of_le
-- name    : GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:15.148801+00:00
-- url     : https://prove2.me/theorems/a98dbedc-b6b0-42ae-a3af-dbede5e71cfa
-- title:
--   Parabolic: cell Rank eq of le
-- statement:
--   The Parabolic construction uses the cell Rank eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L377-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L377-L388

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}

theorem GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le {b : ℕ} (hb : Finset.univ.sup γ ≤ b) (g : GL (Fin n) F) (a : ℕ) :
    cellRank β γ g a b = cellRank β γ g a (Finset.univ.sup γ) := by sorry
