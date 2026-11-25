-- Prove2me | Theorems.Thm_GlobalTheory_Published_chowFormIntExists_iff
-- name    : GlobalTheory.Published.chowFormIntExists_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:28.13972+00:00
-- url     : https://prove2.me/theorems/0a08a4e8-ecad-4c97-bb0f-002d4cfb12c2
-- title:
--   Published: chow Form Int Exists iff
-- statement:
--   The Published construction uses the chow Form Int Exists iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L146-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L146-L154

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

theorem GlobalTheory.Published.chowFormIntExists_iff : ChowFormIntExists ↔
    ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
      P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
      ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 : ℕ) →
      ∃ f : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) f := by sorry
