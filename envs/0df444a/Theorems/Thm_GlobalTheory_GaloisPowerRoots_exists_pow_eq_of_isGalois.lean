-- Prove2me | Theorems.Thm_GlobalTheory_GaloisPowerRoots_exists_pow_eq_of_isGalois
-- name    : GlobalTheory.GaloisPowerRoots.exists_pow_eq_of_isGalois
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:48:48.075536+00:00
-- url     : https://prove2.me/theorems/084cc9d9-ec18-4d89-9d08-893f2f167ed0
-- title:
--   Galois Power Roots: exists pow eq of is Galois
-- statement:
--   The Galois Power Roots construction uses the exists pow eq of is Galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSubMemMaximalIdeal.lean#L184-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSubMemMaximalIdeal.lean#L184-L280

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

theorem GlobalTheory.GaloisPowerRoots.exists_pow_eq_of_isGalois {R : Type*} (K L M : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (hn : IsUnit (Module.finrank K L : R))
    [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K M]
    [FiniteDimensional K M] (ρ : M)
    (hρ : ρ ^ Module.finrank K L = algebraMap K M (algebraMap R K π)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by sorry
