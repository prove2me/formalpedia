-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GLMatrixJoining_om_uGL
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining.om_uGL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:16.3453+00:00
-- url     : https://prove2.me/theorems/5caae693-5442-4de9-9227-bf27cf4e893a
-- title:
--   GLMatrix Joining: om u GL
-- statement:
--   The GLMatrix Joining construction uses the om u GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/GL2CharacterZeros.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/GL2CharacterZeros.lean#L145-L152

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining.om_uGL [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype W] [DecidableEq W] (μ : kˣ →* ℂˣ) (ν : Matrix v ρ k) (ν' : Matrix ρ v k)
    (b : Matrix ρ ρ k) (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) (x : Matrix W (ρ ⊕ v ⊕ ρ) k) :
    om μ (uGL ν ν' b) 1 Φ x = Φ (x * uMat ν ν' b) := by sorry
