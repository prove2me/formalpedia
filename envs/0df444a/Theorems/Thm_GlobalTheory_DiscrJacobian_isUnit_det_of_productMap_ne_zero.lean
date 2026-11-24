-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_isUnit_det_of_productMap_ne_zero
-- name    : GlobalTheory.DiscrJacobian.isUnit_det_of_productMap_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:49:01.441835+00:00
-- url     : https://prove2.me/theorems/54bab53b-619f-4e54-b376-922468cff3de
-- title:
--   Discr Jacobian: is Unit det of product Map ne zero
-- statement:
--   The Discr Jacobian construction uses the is Unit det of product Map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L180-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L180-L248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
open scoped TensorProduct
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
open IsLocalRing

theorem GlobalTheory.DiscrJacobian.isUnit_det_of_productMap_ne_zero [IsLocalRing R]
    [Algebra (ResidueField R) C]
    [IsScalarTower R (ResidueField R) C] {d : ℕ} (b : Module.Basis (Fin d) R B)
    (n : Ideal B) (N : ℕ) (hN : n ^ N ≤ (maximalIdeal R).map (algebraMap R B))
    (ev : B →ₐ[R] ResidueField R) (hev : ∀ w ∈ n, ev w = 0)
    (hgen : ∀ w : B, ∃ c : R, w - algebraMap R B c ∈ n) (ρ : B →ₐ[R] C)
    (De : B ⊗[R] B) (M : Matrix (Fin d) (Fin d) R)
    (hDe : De = ∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j))
    (h : ∀ x : B, De * (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0)
    (H : Algebra.TensorProduct.productMap ρ
      ((IsScalarTower.toAlgHom R (ResidueField R) C).comp ev) De ≠ 0) :
    IsUnit M.det := by sorry
