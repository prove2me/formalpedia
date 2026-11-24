-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_substF_mul
-- name    : GlobalTheory.CompactHowe.substF_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:35.293395+00:00
-- url     : https://prove2.me/theorems/e402e914-9318-4fff-a842-f99efa079f85
-- title:
--   Compact Howe: subst F mul
-- statement:
--   The Compact Howe construction uses the subst F mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixFamilyBilateralSubstitutionCompEqMul.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixFamilyBilateralSubstitutionCompEqMul.lean#L10-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionCompEqMul
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

theorem GlobalTheory.CompactHowe.substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    substF h g (substF h' g' P) = substF (h * h') (g * g') P := by sorry
