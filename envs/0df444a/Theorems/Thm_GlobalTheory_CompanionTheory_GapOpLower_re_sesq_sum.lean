-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapOpLower_re_sesq_sum
-- name    : GlobalTheory.CompanionTheory.GapOpLower.re_sesq_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:58.817778+00:00
-- url     : https://prove2.me/theorems/85e7d04b-7d31-48d4-bf6f-9f562cb0a515
-- title:
--   Gap Op Lower: re sesq sum
-- statement:
--   The Gap Op Lower construction uses the re sesq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCountFromHyperplanes.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCountFromHyperplanes.lean#L8-L12

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpLower
open Finset

theorem GlobalTheory.CompanionTheory.GapOpLower.re_sesq_sum {V ι : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (s t : Finset ι) (f : ι → V) :
    (B (∑ a ∈ s, f a) (∑ b ∈ t, f b)).re = ∑ a ∈ s, ∑ b ∈ t, (B (f a) (f b)).re := by sorry
