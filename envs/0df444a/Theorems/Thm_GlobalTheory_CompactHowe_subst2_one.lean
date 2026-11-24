-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_subst2_one
-- name    : GlobalTheory.CompactHowe.subst2_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:17:02.034007+00:00
-- url     : https://prove2.me/theorems/3f2c1fb8-53d0-49fb-b5f5-0ef41d5d0a2e
-- title:
--   Compact Howe: subst2 one
-- statement:
--   The Compact Howe construction uses the subst2 one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeSubstFLe.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeSubstFLe.lean#L54-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeAevalLeOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe
variable {ι : Type} {N n : ℕ}

theorem GlobalTheory.CompactHowe.subst2_one (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 1 1 P = P := by sorry
