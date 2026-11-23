-- Prove2me | Theorems.Thm_GlobalTheory_EtaleCoordJacobian_chain_rule_and_jacobian_criterion
-- name    : GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:01.343162+00:00
-- url     : https://prove2.me/theorems/58b484b7-1e6c-4ab8-ace4-f0121c81117e
-- title:
--   Etale Coord Jacobian: chain rule and jacobian criterion
-- statement:
--   The Etale Coord Jacobian construction uses the chain rule and jacobian criterion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ChainRuleAndJacobianCriterion.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ChainRuleAndJacobianCriterion.lean#L149-L156

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
open KaehlerDifferential TensorProduct

theorem GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (I : Type) [Fintype I] [DecidableEq I] (t t' : I → B), (MvPolynomial.eval₂Hom c t).Etale → ∃ a : B, (∀ (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C), (∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x) → (∀ i r, d i (c r) = 0) → (Matrix.of fun i j => d i (t' j)).det = φ a * (Matrix.of fun i j => d i (t j)).det) ∧ (IsUnit a → (MvPolynomial.eval₂Hom c t').Etale) := by sorry
