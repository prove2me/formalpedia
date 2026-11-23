-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_approx_mod_squares
-- name    : GlobalTheory.QNorm.exists_approx_mod_squares
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:02.189555+00:00
-- url     : https://prove2.me/theorems/89b4d5a5-47d3-47d6-b2f0-65f953d0e600
-- title:
--   QNorm: exists approx mod squares
-- statement:
--   The QNorm construction uses the exists approx mod squares property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsApproxModLocalSquares.lean#L13-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsApproxModLocalSquares.lean#L13-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquares
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.QNorm.exists_approx_mod_squares :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (z : (F →+* ℝ) → ℝ), (∀ v, y v ≠ 0) → (∀ σ, z σ ≠ 0) → ∃ x : F, x ≠ 0 ∧ (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) x * y v)) ∧ ∀ σ : F →+* ℝ, 0 < σ x * z σ := by sorry
