-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_subst2_mul
-- name    : GlobalTheory.CompactHowe.subst2_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:44.315855+00:00
-- url     : https://prove2.me/theorems/d5b2c396-f3da-4445-b93d-87ae259b61f3
-- title:
--   Compact Howe: subst2 mul
-- statement:
--   The Compact Howe construction uses the subst2 mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeSubstFLe.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeSubstFLe.lean#L41-L52

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

theorem GlobalTheory.CompactHowe.subst2_mul (h h' : Matrix (Fin N) (Fin N) ℂ) (g g' : Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 h g (subst2 h' g' P) = subst2 (h * h') (g * g') P := by sorry
