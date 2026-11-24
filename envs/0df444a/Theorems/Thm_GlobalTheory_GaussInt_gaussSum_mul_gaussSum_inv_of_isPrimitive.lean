-- Prove2me | Theorems.Thm_GlobalTheory_GaussInt_gaussSum_mul_gaussSum_inv_of_isPrimitive
-- name    : GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:55:22.619744+00:00
-- url     : https://prove2.me/theorems/f7bc56c8-71bd-4b2a-a2a8-b54e8ea79c1d
-- title:
--   Gauss Int: gauss Sum mul gauss Sum inv of is Primitive
-- statement:
--   The Gauss Int construction uses the gauss Sum mul gauss Sum inv of is Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussSumMulGaussSumInvOfIsPrimitive.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussSumMulGaussSumInvOfIsPrimitive.lean#L11-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussSumMulGaussSumInvOfIsPrimitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
open GlobalTheory GlobalTheory.GaussInt

theorem GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive {K : Type} [Field K] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter K N} {ψ : AddChar (ZMod N) K} (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (N : K) := by sorry
