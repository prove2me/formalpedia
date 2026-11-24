-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_eq_blockOne_of_col
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.eq_blockOne_of_col
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:19.849286+00:00
-- url     : https://prove2.me/theorems/664b894c-be94-42e6-887b-739fa1fd6301
-- title:
--   Stab First: eq block One of col
-- statement:
--   The Stab First construction uses the eq block One of col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L82-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L82-L100

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {K : Type} [CommRing K] {M : ℕ}

theorem GlobalTheory.CompanionTheory.SW.StabFirst.eq_blockOne_of_col (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) {s : K} (hs : IsUnit s)
    {h : Matrix (Fin (M + 1)) (Fin (M + 1)) K} (hm : cT σ h * blockOne s J * h = blockOne s J)
    (h00 : h 0 0 = 1) (hi0 : ∀ i : Fin M, h i.succ 0 = 0) :
    h = blockOne 1 (h.submatrix Fin.succ Fin.succ) := by sorry
