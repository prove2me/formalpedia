-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_exists_of_charpoly
-- name    : GlobalTheory.ClassParam.HidaSetting.exists_of_charpoly
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:13:42.467832+00:00
-- url     : https://prove2.me/theorems/78564fea-6462-4a0c-a774-ce91cd84b0b5
-- title:
--   Hida Setting: exists of charpoly
-- statement:
--   The Hida Setting construction uses the exists of charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L384-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L384-L462

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

theorem GlobalTheory.ClassParam.HidaSetting.exists_of_charpoly [IsArtinianRing A] (S : HidaSetting σ τ α b) (hJ : IsHerm σ J)
    (hd : IsUnit J.det) (g : UJ σ J)
    (hg : ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A).charpoly
      = (Algebra.leftMulMatrix b α).charpoly)
    (hs : (Algebra.leftMulMatrix b α).charpoly.Separable) :
    ∃ x φ, IsUnit x ∧ τ x = x ∧ Iso σ τ J x φ ∧
      Intw α ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ := by sorry
