-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_contr_isHomogeneous
-- name    : GlobalTheory.RegBound.contr_isHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:44.085588+00:00
-- url     : https://prove2.me/theorems/f71524ff-cb8e-4c61-a285-a9c58c30bb6b
-- title:
--   Reg Bound: contr is Homogeneous
-- statement:
--   The Reg Bound construction uses the contr is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L522-L525
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L522-L525

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

theorem GlobalTheory.RegBound.contr_isHomogeneous (φ : L →ₗ[K] K) {e : ℕ} {F : MvPolynomial σ L}
    (hF : F.IsHomogeneous e) : (contr φ F).IsHomogeneous e := by sorry
