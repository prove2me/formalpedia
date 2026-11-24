-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NormPrime_norm_one_tmul
-- name    : GlobalTheory.CompanionTheory.NormPrime.norm_one_tmul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:16.871813+00:00
-- url     : https://prove2.me/theorems/e9314017-f575-4e3e-a80e-9b9a633c50be
-- title:
--   Norm Prime: norm one tmul
-- statement:
--   The Norm Prime construction uses the norm one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/NormNotMemPrimeIff.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/NormNotMemPrimeIff.lean#L14-L23

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
open TensorProduct

theorem GlobalTheory.CompanionTheory.NormPrime.norm_one_tmul {A B K : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] [Field K] [Algebra A K] (e : B) :
    Algebra.norm K ((1 : K) ⊗ₜ[A] e : K ⊗[A] B) = algebraMap A K (Algebra.norm A e) := by sorry
