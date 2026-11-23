-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_mul_split
-- name    : GlobalTheory.CompanionTheory.SplitExtLat.mul_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:17.824518+00:00
-- url     : https://prove2.me/theorems/0d3e1b04-c11f-4cda-b3f9-c47cb723dc62
-- title:
--   Split Ext Lat: mul split
-- statement:
--   The Split Ext Lat construction uses the mul split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitHomeoApply.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitHomeoApply.lean#L41-L45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitExtLat
variable {P G₁ : Type} [Group P] [Group G₁]

theorem GlobalTheory.CompanionTheory.SplitExtLat.mul_split (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) (g : P) (m : π.ker) (u : G₁) :
    g * ((m : P) * ι u) =
      ((kerPart ι π h g * MulAut.conjNormal (ι (π g)) m : π.ker) : P) * ι (π g * u) := by sorry
