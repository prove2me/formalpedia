-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_succ_succ
-- name    : GlobalTheory.CompanionTheory.SW.BlockAlg.blockOne_succ_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:35.051322+00:00
-- url     : https://prove2.me/theorems/d180096c-a54d-4c76-a34e-5dcd662f8c73
-- title:
--   Block Alg: block One succ succ
-- statement:
--   The Block Alg construction uses the block One succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L19-L19

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

theorem GlobalTheory.CompanionTheory.SW.BlockAlg.blockOne_succ_succ (i j : Fin M) : blockOne t A i.succ j.succ = A i j := by sorry
