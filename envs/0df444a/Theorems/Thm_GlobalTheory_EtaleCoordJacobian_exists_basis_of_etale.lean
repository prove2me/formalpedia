-- Prove2me | Theorems.Thm_GlobalTheory_EtaleCoordJacobian_exists_basis_of_etale
-- name    : GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:03.570416+00:00
-- url     : https://prove2.me/theorems/e7b33613-cdab-4d69-9573-4fe8241c0a07
-- title:
--   Etale Coord Jacobian: exists basis of etale
-- statement:
--   The Etale Coord Jacobian construction uses the exists basis of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ChainRuleAndJacobianCriterion.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ChainRuleAndJacobianCriterion.lean#L23-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KaehlerDifferential TensorProduct
open GlobalTheory GlobalTheory.EtaleCoordJacobian
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]
open KaehlerDifferential TensorProduct
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]

theorem GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale [Finite I] [Algebra.Etale (MvPolynomial I R) B] :
    (∃ b : Module.Basis I B Ω[B⁄R],
      ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) ∧
      Algebra.Smooth R B := by sorry
