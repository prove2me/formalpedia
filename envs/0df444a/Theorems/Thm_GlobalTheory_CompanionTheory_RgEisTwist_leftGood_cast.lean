-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_leftGood_cast
-- name    : GlobalTheory.CompanionTheory.RgEisTwist.leftGood_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:13.143489+00:00
-- url     : https://prove2.me/theorems/3e96fe1a-0095-4969-9bdc-f9549e8a2126
-- title:
--   Rg Eis Twist: left Good cast
-- statement:
--   The Rg Eis Twist construction uses the left Good cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistOfSectionLaw.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistOfSectionLaw.lean#L74-L82

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

theorem GlobalTheory.CompanionTheory.RgEisTwist.leftGood_cast {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {A B : Submodule ℂ W} (e : A = B)
    {Op : ℂ → (X →L[ℂ] A)} {a : ℝ} (hO : LeftGood Op a) :
    LeftGood (fun z => (castL e).comp (Op z)) a := by sorry
