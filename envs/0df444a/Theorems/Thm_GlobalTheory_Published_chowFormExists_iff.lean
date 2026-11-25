-- Prove2me | Theorems.Thm_GlobalTheory_Published_chowFormExists_iff
-- name    : GlobalTheory.Published.chowFormExists_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:10:52.64859+00:00
-- url     : https://prove2.me/theorems/1f8f29ee-47ed-42e3-8e9b-82c9e1496f45
-- title:
--   Published: chow Form Exists iff
-- statement:
--   The Published construction uses the chow Form Exists iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L134-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L134-L144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.Published
open GlobalTheory.ChowHt

theorem GlobalTheory.Published.chowFormExists_iff : ChowFormExists ↔
    ∀ (k : Type) [Field k] [CharZero k] (N D : ℕ) (I : Ideal (MvPolynomial (Fin N) k)),
      I.IsHomogeneous (homogeneousSubmodule (Fin N) k) →
      (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
        MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k))).IsPrime →
      ringKrullDim (MvPolynomial (Fin N) k ⧸ I) = (D + 1 : ℕ) →
      ∃ f : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) f := by sorry
