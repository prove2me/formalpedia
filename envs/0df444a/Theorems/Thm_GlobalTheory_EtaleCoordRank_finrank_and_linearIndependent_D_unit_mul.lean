-- Prove2me | Theorems.Thm_GlobalTheory_EtaleCoordRank_finrank_and_linearIndependent_D_unit_mul
-- name    : GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:59:07.961152+00:00
-- url     : https://prove2.me/theorems/84de8981-889f-4bc8-8167-a6dfe88e53c4
-- title:
--   Etale Coord Rank: finrank and linear Independent D unit mul
-- statement:
--   The Etale Coord Rank construction uses the finrank and linear Independent D unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleCoordinatesDifferentials.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleCoordinatesDifferentials.lean#L9-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinatesDifferentials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory GlobalTheory.EtaleCoordRank
open KaehlerDifferential TensorProduct

theorem GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by sorry
