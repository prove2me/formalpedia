-- Prove2me | Theorems.Thm_GlobalTheory_GaloisPowerRoots_exists_unit_mul_pow
-- name    : GlobalTheory.GaloisPowerRoots.exists_unit_mul_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:48:53.289442+00:00
-- url     : https://prove2.me/theorems/7463bb20-ea6d-4003-ab30-f8d4411cd11f
-- title:
--   Galois Power Roots: exists unit mul pow
-- statement:
--   The Galois Power Roots construction uses the exists unit mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSubMemMaximalIdeal.lean#L143-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSubMemMaximalIdeal.lean#L143-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Polynomial IsLocalRing
open scoped Pointwise
open GlobalTheory GlobalTheory.GaloisPowerRoots

theorem GlobalTheory.GaloisPowerRoots.exists_unit_mul_pow {R : Type*} (K L : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAlgClosed (ResidueField R)] [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosure R L)] :
    ∃ (u : (integralClosure R L)ˣ) (ϖ : integralClosure R L),
      algebraMap R _ π = u * ϖ ^ Module.finrank K L := by sorry
