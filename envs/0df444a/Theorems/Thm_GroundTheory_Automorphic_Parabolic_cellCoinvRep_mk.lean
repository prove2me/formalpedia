-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellCoinvRep_mk
-- name    : GroundTheory.Automorphic.Parabolic.cellCoinvRep_mk
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:34.400951+00:00
-- url     : https://prove2.me/theorems/ae5d0592-d74f-4da5-bef6-b8e745dab6f3
-- title:
--   Parabolic: cell Coinv Rep mk
-- statement:
--   The Parabolic construction uses the cell Coinv Rep mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L362-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L362-L364

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

theorem GroundTheory.Automorphic.Parabolic.cellCoinvRep_mk (b : cellLeviParabolic F β γ w) (v : W) :
    cellCoinvRep σ b (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (cellRepM β γ w σ b v) := by sorry
