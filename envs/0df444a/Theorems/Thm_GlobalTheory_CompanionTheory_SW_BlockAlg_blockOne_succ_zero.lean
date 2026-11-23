-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_succ_zero
-- name    : GlobalTheory.CompanionTheory.SW.BlockAlg.blockOne_succ_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:47.195423+00:00
-- url     : https://prove2.me/theorems/5506a3d8-b894-41dc-949d-df67f0dbce5c
-- title:
--   Block Alg: block One succ zero
-- statement:
--   The Block Alg construction uses the block One succ zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L17-L17

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockAlg
variable {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)

theorem GlobalTheory.CompanionTheory.SW.BlockAlg.blockOne_succ_zero (i : Fin M) : blockOne t A i.succ 0 = 0 := by sorry
