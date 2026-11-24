-- Prove2me | Theorems.Thm_GlobalTheory_T_charpoly_mulLeft_eq_map_of_span_range_eq
-- name    : GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:39.352558+00:00
-- url     : https://prove2.me/theorems/d7192f03-2d17-45a2-b88f-ccef8d87fd4e
-- title:
--   T: charpoly mul Left eq map of span range eq
-- statement:
--   The T construction uses the charpoly mul Left eq map of span range eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyMulLeftEqMapOfSpanningLatticeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyMulLeftEqMapOfSpanningLatticeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftEqMapOfSpanningLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftEqMapOfSpanningLatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq : ∀ (R F A S : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A] [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S] [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A), Function.Injective ι → Submodule.span F (Set.range ι) = ⊤ → ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly = ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by sorry
