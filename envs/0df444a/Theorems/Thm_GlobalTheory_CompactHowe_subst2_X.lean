-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_subst2_X
-- name    : GlobalTheory.CompactHowe.subst2_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:20.700457+00:00
-- url     : https://prove2.me/theorems/472d753a-7142-49c2-97fc-5bc3f748ba49
-- title:
--   Compact Howe: subst2 X
-- statement:
--   The Compact Howe construction uses the subst2 X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeSubstFLe.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeSubstFLe.lean#L20-L21

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

theorem GlobalTheory.CompactHowe.subst2_X (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (p : Fin N × Fin n) :
    subst2 h g (X p) = ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l) := by sorry
