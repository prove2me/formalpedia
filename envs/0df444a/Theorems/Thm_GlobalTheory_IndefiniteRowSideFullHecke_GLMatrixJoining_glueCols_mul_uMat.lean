-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GLMatrixJoining_glueCols_mul_uMat
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining.glueCols_mul_uMat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:01.723806+00:00
-- url     : https://prove2.me/theorems/34cd684e-e845-4f45-adf4-8d8dc090c412
-- title:
--   GLMatrix Joining: glue Cols mul u Mat
-- statement:
--   The GLMatrix Joining construction uses the glue Cols mul u Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/GL2CharacterZeros.lean#L138-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/GL2CharacterZeros.lean#L138-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.SplitWeil
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
variable {k : Type} [Field k]
variable {ρ v W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]

theorem GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining.glueCols_mul_uMat (ξ : Matrix W ρ k) (x₀ : Matrix W v k) (c : Matrix W ρ k)
    (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k) :
    glueCols ξ x₀ c * uMat ν ν' b = glueCols ξ (x₀ + ξ * ν') (c + ξ * b + x₀ * ν) := by sorry
