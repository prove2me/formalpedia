-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_kummer_galois
-- name    : GlobalTheory.CNorm.kummer_galois
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:07.002073+00:00
-- url     : https://prove2.me/theorems/e4695101-8b4b-422f-ab70-1c09ad1a8e3f
-- title:
--   CNorm: kummer galois
-- statement:
--   The CNorm construction uses the kummer galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/KummerGalois.lean#L23-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/KummerGalois.lean#L23-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_KummerGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.kummer_galois : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ IsGalois F E ∧ orderOf σ = p ∧ (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) ∧ Nonempty (E ≃ₐ[F] AdjoinRoot (X ^ p - C δ : F[X])) ∧ ∀ (L : Type) [Field L] [Algebra F L] (r : L), r ^ p = algebraMap F L δ → ∃ ψ : E →ₐ[F] L, ψ θ = r := by sorry
