-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_normB_apply
-- name    : GlobalTheory.WeylDuality.normB_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:57.322107+00:00
-- url     : https://prove2.me/theorems/4957882c-17d5-4909-90a6-72e1699d462d
-- title:
--   Weyl Duality: norm B apply
-- statement:
--   The Weyl Duality construction uses the norm B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L201-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L201-L202

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality

theorem GlobalTheory.WeylDuality.normB_apply {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (x y : dualWeyl ℚ r n ν) :
    normB hn ν x y = (fockQ (hw ℚ hn ν) (hw ℚ hn ν))⁻¹ * fockQ x.1 y.1 := by sorry
