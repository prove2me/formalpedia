-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_ch_cont
-- name    : GlobalTheory.CompanionTheory.RgEisTwist.ch_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:05.048136+00:00
-- url     : https://prove2.me/theorems/ee3c1a83-4ec4-4e70-a63d-8cefe1950e8a
-- title:
--   Rg Eis Twist: ch cont
-- statement:
--   The Rg Eis Twist construction uses the ch cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistOfSectionLaw.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistOfSectionLaw.lean#L25-L28

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistOfSectionLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisTwist
open PositivityTheory.RgEis
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K : Subgroup G} {c₀ : G → ℂ}

theorem GlobalTheory.CompanionTheory.RgEisTwist.ch_cont (h : IsCh Γ ⊤ c₀) : Continuous c₀ := by sorry
