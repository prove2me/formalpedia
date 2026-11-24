-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Nbhd_finiteFreeHom_algebraMap_iff
-- name    : GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:49.816177+00:00
-- url     : https://prove2.me/theorems/ca685f8c-39ea-4e6b-9542-8fb896dd9f04
-- title:
--   Nbhd: finite Free Hom algebra Map iff
-- statement:
--   The Nbhd construction uses the finite Free Hom algebra Map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFreePullbackAffine.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFreePullbackAffine.lean#L13-L17

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

theorem GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff {A B : Type} [CommRing A] [CommRing B] [Algebra A B] :
    FiniteFreeHom (algebraMap A B) ↔ Module.Free A B ∧ Module.Finite A B := by sorry
