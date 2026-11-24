-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_charpoly_of_intw
-- name    : GlobalTheory.ClassParam.charpoly_of_intw
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:13:33.083797+00:00
-- url     : https://prove2.me/theorems/3efebc2e-74ba-4c6d-96aa-fb18bd1196fe
-- title:
--   Class Param: charpoly of intw
-- statement:
--   The Class Param construction uses the charpoly of intw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L374-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L374-L382

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}

theorem GlobalTheory.ClassParam.charpoly_of_intw {g : Matrix (Fin r) (Fin r) A} {φ : B ≃ₗ[A] (Fin r → A)}
    (b : Module.Basis (Fin r) A B)
    (hg : Intw α g φ) : g.charpoly = (Algebra.leftMulMatrix b α).charpoly := by sorry
