-- Prove2me | Theorems.Thm_GlobalTheory_GaloisPowerRoots_exists_pow_finrank_eq
-- name    : GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:48:47.152994+00:00
-- url     : https://prove2.me/theorems/7e3ee93d-4c65-4309-8ad5-d751287a3bd1
-- title:
--   Galois Power Roots: exists pow finrank eq
-- statement:
--   The Galois Power Roots construction uses the exists pow finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSubMemMaximalIdeal.lean#L298-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSubMemMaximalIdeal.lean#L298-L318

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

theorem GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq {R : Type} (K : Type u_1) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hn : IsUnit (Module.finrank K L : R)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by sorry
