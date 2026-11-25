-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_clip
-- name    : GroundTheory.Automorphic.Parabolic.cellRank_clip
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:17.959485+00:00
-- url     : https://prove2.me/theorems/150436d0-bb5a-4ed6-a150-6499fa4746ae
-- title:
--   Parabolic: cell Rank clip
-- statement:
--   The Parabolic construction uses the cell Rank clip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L390-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L390-L398

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

theorem GroundTheory.Automorphic.Parabolic.cellRank_clip (g : GL (Fin n) F) (a b : ℕ) :
    cellRank β γ g a b =
      cellRank β γ g (min a (Finset.univ.sup β + 1)) (min b (Finset.univ.sup γ)) := by sorry
