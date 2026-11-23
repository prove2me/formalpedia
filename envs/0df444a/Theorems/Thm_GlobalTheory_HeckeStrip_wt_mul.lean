-- Prove2me | Theorems.Thm_GlobalTheory_HeckeStrip_wt_mul
-- name    : GlobalTheory.HeckeStrip.wt_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:42.354001+00:00
-- url     : https://prove2.me/theorems/c12456d3-d4c4-48b7-b162-41451f5cdf33
-- title:
--   Hecke Strip: wt mul
-- statement:
--   The Hecke Strip construction uses the wt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormWt.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormWt.lean#L22-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

theorem GlobalTheory.HeckeStrip.wt_mul (φ : I → K →+* ℂ) (n : I → ℤ) (a b : K) : wt φ n (a * b) = wt φ n a * wt φ n b := by sorry
