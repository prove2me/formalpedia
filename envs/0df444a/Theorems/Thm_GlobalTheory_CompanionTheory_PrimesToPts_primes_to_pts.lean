-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrimesToPts_primes_to_pts
-- name    : GlobalTheory.CompanionTheory.PrimesToPts.primes_to_pts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:08.453808+00:00
-- url     : https://prove2.me/theorems/aeecb745-e430-4966-beb7-b8ebc6be235c
-- title:
--   Primes To Pts: primes to pts
-- statement:
--   The Primes To Pts construction uses the primes to pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/BasicOpenNormFibreIff.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/BasicOpenNormFibreIff.lean#L31-L44

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_BasicOpenNormFibreIff
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesToPts

theorem GlobalTheory.CompanionTheory.PrimesToPts.primes_to_pts : ∀ {P D : Scheme.{0}} [IsAffine P] [IsAffine D] (v : P ⟶ D) (N : Γ(D, ⊤)) (e : Γ(P, ⊤)), (∀ p : PrimeSpectrum Γ(D, ⊤), N ∉ p.asIdeal ↔ ∀ q : PrimeSpectrum Γ(P, ⊤), q.asIdeal.comap v.appTop.hom = p.asIdeal → e ∉ q.asIdeal) → ∀ y : D, y ∈ D.basicOpen N ↔ ∀ z : P, v z = y → z ∈ P.basicOpen e := by sorry
