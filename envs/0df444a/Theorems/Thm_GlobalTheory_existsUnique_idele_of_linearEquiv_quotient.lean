-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_idele_of_linearEquiv_quotient
-- name    : GlobalTheory.existsUnique_idele_of_linearEquiv_quotient
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:11.653868+00:00
-- url     : https://prove2.me/theorems/7def1d38-aaa8-4836-8677-cb3dca48aa75
-- title:
--   Global Theory: exists Unique idele of linear Equiv quotient
-- statement:
--   The Global Theory construction uses the exists Unique idele of linear Equiv quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L796-L808
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L796-L808

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

theorem GlobalTheory.existsUnique_idele_of_linearEquiv_quotient {K : Type*} [Field K] [NumberField K]
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
    (φ : (K ⧸ ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) →ₗ[𝓞 K]
      (K ⧸ (𝔞 : Submodule (𝓞 K) K))) (hφ : Function.Bijective φ) :
    ∃! t : (FiniteAdeleRing (𝓞 K) K)ˣ, ∃ h : 𝔞 = t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K),
      ∀ q, φ q = mulEquiv t⁻¹ one_ne_zero h q := by sorry
