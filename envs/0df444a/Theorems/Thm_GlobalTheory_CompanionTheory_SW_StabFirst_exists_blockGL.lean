-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_exists_blockGL
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.exists_blockGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:51.477198+00:00
-- url     : https://prove2.me/theorems/e4a444cc-c1e4-4c5c-8f9e-d378fc6ded6f
-- title:
--   Stab First: exists block GL
-- statement:
--   The Stab First construction uses the exists block GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L102-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L102-L131

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

theorem GlobalTheory.CompanionTheory.SW.StabFirst.exists_blockGL (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) {s : K} (hs : IsUnit s)
    {h : GL (Fin (M + 1)) K} (hm : h ∈ UJ σ (blockOne s J))
    (h00 : (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) 0 0 = 1)
    (hi0 : ∀ i : Fin M, (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) i.succ 0 = 0) :
    ∃ g : GL (Fin M) K, blockGL g = h := by sorry
