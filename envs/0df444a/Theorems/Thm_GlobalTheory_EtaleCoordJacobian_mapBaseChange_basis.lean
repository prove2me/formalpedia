-- Prove2me | Theorems.Thm_GlobalTheory_EtaleCoordJacobian_mapBaseChange_basis
-- name    : GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:20.01049+00:00
-- url     : https://prove2.me/theorems/93feabfc-33fa-464d-a339-2f14c07ae06d
-- title:
--   Etale Coord Jacobian: map Base Change basis
-- statement:
--   The Etale Coord Jacobian construction uses the map Base Change basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ChainRuleAndJacobianCriterion.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ChainRuleAndJacobianCriterion.lean#L14-L18

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

theorem GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis (i : I) :
    mapBaseChange R (MvPolynomial I R) B (((mvPolynomialBasis R I).baseChange B) i) =
      D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i)) := by sorry
