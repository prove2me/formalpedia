-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Nbhd_finiteFreeHom_stableUnderComposition
-- name    : GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_stableUnderComposition
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:32.893614+00:00
-- url     : https://prove2.me/theorems/ededa3ca-354b-494f-a2b9-e2e36896c21e
-- title:
--   Nbhd: finite Free Hom stable Under Composition
-- statement:
--   The Nbhd construction uses the finite Free Hom stable Under Composition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFreePullbackAffine.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFreePullbackAffine.lean#L36-L40

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreePullbackAffine
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

theorem GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_stableUnderComposition :
    RingHom.StableUnderComposition (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) := by sorry
