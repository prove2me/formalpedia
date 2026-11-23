-- Prove2me | Theorems.Thm_GlobalTheory_exists_ringKrullDim_quotient_mvPolynomial_eq_nat
-- name    : GlobalTheory.exists_ringKrullDim_quotient_mvPolynomial_eq_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:38.986429+00:00
-- url     : https://prove2.me/theorems/3bda996a-860a-42f6-9bcb-3b669c78e263
-- title:
--   Global Theory: exists ring Krull Dim quotient mv Polynomial eq nat
-- statement:
--   The Global Theory construction uses the exists ring Krull Dim quotient mv Polynomial eq nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L305-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L305-L318

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ : Type*} [Finite σ] {k : Type*} [Field k]

theorem GlobalTheory.exists_ringKrullDim_quotient_mvPolynomial_eq_nat {I : Ideal (MvPolynomial σ k)}
    (hI : I ≠ ⊤) : ∃ δ : ℕ, ringKrullDim (MvPolynomial σ k ⧸ I) = δ := by sorry
