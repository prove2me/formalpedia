-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_mem_span_of_mu_eq_zero
-- name    : GlobalTheory.DiscrJacobian.mem_span_of_mu_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:51:20.13348+00:00
-- url     : https://prove2.me/theorems/2f32adfd-711b-4865-9c05-1c68c357f350
-- title:
--   Discr Jacobian: mem span of mu eq zero
-- statement:
--   The Discr Jacobian construction uses the mem span of mu eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L30-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L30-L117

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
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]
open scoped TensorProduct
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]

theorem GlobalTheory.DiscrJacobian.mem_span_of_mu_eq_zero {ι : Type} [Fintype ι] [Module.Finite R B]
    [Module.FinitePresentation S B] (x : ι → S)
    (hx : ∀ j, x j ∈ (⊥ : Ideal S).jacobson)
    (hgen : ∀ s : S, ∃ (c : R) (u : ι → S), s = algebraMap R S c + ∑ j, x j * u j)
    (z : S ⊗[R] B) (hz : _root_.GlobalTheory.DiscrJacobian.mu R S B z = 0) :
    z ∈ Ideal.span (Set.range fun j => x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j)) := by sorry
