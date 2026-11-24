-- Prove2me | Theorems.Thm_GlobalTheory_SqDet_exists_orthonormal_of_diag_pos_isSquare
-- name    : GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:22:23.039716+00:00
-- url     : https://prove2.me/theorems/ba78010a-864d-44ea-9088-297c65bbad7f
-- title:
--   Sq Det: exists orthonormal of diag pos is Square
-- statement:
--   The Sq Det construction uses the exists orthonormal of diag pos is Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsOrthonormalHermitianOfDiagPosIsSquare.lean#L226-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsOrthonormalHermitianOfDiagPosIsSquare.lean#L226-L230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandherrAndLandherrSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsOrthonormalHermitianOfDiagPosIsSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.SqDet
open NumberField
open scoped Matrix ComplexConjugate

theorem GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare :
    ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (d : ℕ) (θ : K), 0 < d → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) → (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) → ∃ e : Fin r → V, ∀ i j, h (e i) (e j) = if i = j then 1 else 0 := by sorry
