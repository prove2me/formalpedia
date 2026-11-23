-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_BlockMul_blocks_mul
-- name    : GlobalTheory.CompanionTheory.QL.BlockMul.blocks_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:54.145523+00:00
-- url     : https://prove2.me/theorems/e98aeac5-ff38-4149-a700-1410146237c1
-- title:
--   Block Mul: blocks mul
-- statement:
--   The Block Mul construction uses the blocks mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlockMatrixMulBlocks.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlockMatrixMulBlocks.lean#L7-L11

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.BlockMul

theorem GlobalTheory.CompanionTheory.QL.BlockMul.blocks_mul : ∀ {F : Type} [Field F] (r d c e : ℕ) (x : Matrix (Fin (r + d)) (Fin (r + c)) F) (y : Matrix (Fin (r + c)) (Fin (r + e)) F), bAA (x * y) = bAA x * bAA y + bAD x * bDA y ∧ bAD (x * y) = bAA x * bAD y + bAD x * bDD y ∧ bDA (x * y) = bDA x * bAA y + bDD x * bDA y ∧ bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by sorry
