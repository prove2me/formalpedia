-- Prove2me | Theorems.Thm_GlobalTheory_charpoly_mulLeft_eq_map_of_spanning_lattice
-- name    : GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:46.041009+00:00
-- url     : https://prove2.me/theorems/ae6c11d5-c3bf-45d3-a5aa-2a3a3dea1a78
-- title:
--   Global Theory: charpoly mul Left eq map of spanning lattice
-- statement:
--   The Global Theory construction uses the charpoly mul Left eq map of spanning lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyMulLeftEqMapOfSpanningLattice.lean#L6-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyMulLeftEqMapOfSpanningLattice.lean#L6-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftEqMapOfSpanningLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice (R F A S : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A]
    [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S]
    [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A) (hι : Function.Injective ι)
    (hspan : Submodule.span F (Set.range ι) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly =
      ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by sorry
