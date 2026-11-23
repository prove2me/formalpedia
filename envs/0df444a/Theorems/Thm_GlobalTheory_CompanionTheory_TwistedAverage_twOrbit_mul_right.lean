-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_twOrbit_mul_right
-- name    : GlobalTheory.CompanionTheory.TwistedAverage.twOrbit_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:01.843891+00:00
-- url     : https://prove2.me/theorems/877a36b5-5a5c-4394-9833-752d4409862b
-- title:
--   Twisted Average: tw Orbit mul right
-- statement:
--   The Twisted Average construction uses the tw Orbit mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemTwKerIffAverage.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemTwKerIffAverage.lean#L72-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.TwistedAverage.twOrbit_mul_right (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V)
    (t k : L) (hk : k ∈ stabKer ρ L θ x) : twOrbit ρ L θ x (t * k) = twOrbit ρ L θ x t := by sorry
