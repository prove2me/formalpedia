-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_contr_comp
-- name    : GlobalTheory.RegBound.contr_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:23.203639+00:00
-- url     : https://prove2.me/theorems/959e5bc9-61c7-473c-ac3b-e4aeb3bb0a90
-- title:
--   Reg Bound: contr comp
-- statement:
--   The Reg Bound construction uses the contr comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L428-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L428-L433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]

theorem GlobalTheory.RegBound.contr_comp (φ : L →ₗ[K] K) (e : ℕ) (F : MvPolynomial σ L) :
    contr φ (homogeneousComponent e F) = homogeneousComponent e (contr φ F) := by sorry
