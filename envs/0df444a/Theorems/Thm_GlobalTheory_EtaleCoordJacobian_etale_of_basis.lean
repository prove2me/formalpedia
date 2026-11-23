-- Prove2me | Theorems.Thm_GlobalTheory_EtaleCoordJacobian_etale_of_basis
-- name    : GlobalTheory.EtaleCoordJacobian.etale_of_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:58.391022+00:00
-- url     : https://prove2.me/theorems/a41215ba-ceb0-4976-a292-fb852ce2891a
-- title:
--   Etale Coord Jacobian: etale of basis
-- statement:
--   The Etale Coord Jacobian construction uses the etale of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ChainRuleAndJacobianCriterion.lean#L37-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ChainRuleAndJacobianCriterion.lean#L37-L71

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

theorem GlobalTheory.EtaleCoordJacobian.etale_of_basis [Finite I] [Algebra.Smooth R B]
    (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) :
    Algebra.Etale (MvPolynomial I R) B := by sorry
