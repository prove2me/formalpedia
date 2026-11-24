-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_WeakApprox_core
-- name    : GlobalTheory.UnRep.WeakApprox.core
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:21:33.263118+00:00
-- url     : https://prove2.me/theorems/e83aa832-03c7-40f2-a99b-7c8b57c6040e
-- title:
--   Weak Approx: core
-- statement:
--   The Weak Approx construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L93-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L93-L210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.WeakApprox

theorem GlobalTheory.UnRep.WeakApprox.core {K R : Type} [Field K] [CommRing R] (ι : K →+* R) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : (G.map c)ᵀ = G) (hdet : G.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (O : Subring (Matrix (Fin n) (Fin n) R)) (hb : ∀ M, ∃ d : ℕ, 0 < d ∧ d • M ∈ O)
    (e : R) (he : e * e = e) (hσe : σ e = e) (he0 : e ≠ 0) (heO : ∀ X ∈ O, e • X ∈ O)
    (N : ℕ) (hN : 0 < N) (hnak : ∀ X ∈ O, ∃ W ∈ O, (1 + e • (N • X)) * W = 1)
    (hapx : ∀ (M : Matrix (Fin n) (Fin n) R) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) K, ∃ X ∈ O,
      (M - (G.map ι * M.map σ * (G.map ι)⁻¹)ᵀ) -
        (M₀.map ι - (G.map ι * (M₀.map ι).map σ * (G.map ι)⁻¹)ᵀ) = D • X)
    (g h : Matrix (Fin n) (Fin n) R) (hg : h * g = 1) (hh : hᵀ * G.map ι * h.map σ = G.map ι)
    (lam : K) (hlam : lam * c lam = 1)
    (hu : IsUnit (1 + ι lam • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R))).det)
    (D : ℕ) (hD : 0 < D) :
    ∃ γ : Matrix (Fin n) (Fin n) K, γᵀ * G * γ.map c = G ∧
      ∃ X ∈ O, e • (γ.map ι * g - 1) = D • X := by sorry
