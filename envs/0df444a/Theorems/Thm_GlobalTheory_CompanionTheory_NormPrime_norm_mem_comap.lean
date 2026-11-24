-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NormPrime_norm_mem_comap
-- name    : GlobalTheory.CompanionTheory.NormPrime.norm_mem_comap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:07.0528+00:00
-- url     : https://prove2.me/theorems/7dc8d3e9-a938-428d-a210-3fa931116513
-- title:
--   Norm Prime: norm mem comap
-- statement:
--   The Norm Prime construction uses the norm mem comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/NormNotMemPrimeIff.lean#L25-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/NormNotMemPrimeIff.lean#L25-L41

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_NormNotMemPrimeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NormPrime

theorem GlobalTheory.CompanionTheory.NormPrime.norm_mem_comap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (e : B) (q : Ideal B) (he : e ∈ q) :
    Algebra.norm A e ∈ q.comap (algebraMap A B) := by sorry
