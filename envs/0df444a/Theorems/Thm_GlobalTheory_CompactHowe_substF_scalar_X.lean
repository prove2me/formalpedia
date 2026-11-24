-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_substF_scalar_X
-- name    : GlobalTheory.CompactHowe.substF_scalar_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:32.045054+00:00
-- url     : https://prove2.me/theorems/d64787e0-1770-4e3e-aee3-f7426b6fefd7
-- title:
--   Compact Howe: subst F scalar X
-- statement:
--   The Compact Howe construction uses the subst F scalar X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixFamilyBilateralSubstitutionScalarMonomial.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixFamilyBilateralSubstitutionScalarMonomial.lean#L9-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionScalarMonomial
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

theorem GlobalTheory.CompactHowe.substF_scalar_X {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (p : ι × Fin N × Fin n) :
    substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (X p)
      = C (if p.1 = τ₀ then ζ else 1) * X p := by sorry
