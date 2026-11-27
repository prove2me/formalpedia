-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_idele_of_linearEquiv_quotient_local
-- name    : GlobalTheory.existsUnique_idele_of_linearEquiv_quotient_local
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:20.603291+00:00
-- url     : https://prove2.me/theorems/c11f54bf-550c-57cf-a16c-aa2f4bb59c58
-- title:
--   Global Theory: exists Unique idele of linear Equiv quotient local
-- statement:
--   The Global Theory construction uses the exists Unique idele of linear Equiv quotient local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L810-L840
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L810-L840

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory
open NumberField GlobalTheory.Idele

theorem GlobalTheory.existsUnique_idele_of_linearEquiv_quotient_local {K : Type*} [Field K] [NumberField K]
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
    (φ : (K ⧸ ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) →ₗ[𝓞 K]
      (K ⧸ (𝔞 : Submodule (𝓞 K) K))) (hφ : Function.Bijective φ) :
    ∃! t : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (∀ x : K, x ∈ 𝔞 ↔ ∀ v, (t : FiniteAdeleRing (𝓞 K) K) v * algebraMap K (v.adicCompletion K) x
        ∈ v.adicCompletionIntegers K) ∧
      ∀ x y : K, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
        ∀ v, ((t⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v *
          algebraMap K (v.adicCompletion K) x - algebraMap K (v.adicCompletion K) y ∈
            localIdeal v 𝔞 := by sorry
