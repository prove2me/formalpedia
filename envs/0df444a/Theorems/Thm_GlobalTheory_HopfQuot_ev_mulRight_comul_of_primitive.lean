-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_ev_mulRight_comul_of_primitive
-- name    : GlobalTheory.HopfQuot.ev_mulRight_comul_of_primitive
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:29.07995+00:00
-- url     : https://prove2.me/theorems/fc71d7eb-0b46-5286-88b8-b454d7ea6a40
-- title:
--   Hopf Quot: ev mul Right comul of primitive
-- statement:
--   The Hopf Quot construction uses the ev mul Right comul of primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoactionEqAddOfPrimitive.lean#L12-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoactionEqAddOfPrimitive.lean#L12-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoactionEqAddOfPrimitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory GlobalTheory.HopfQuot
variable {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]

theorem GlobalTheory.HopfQuot.ev_mulRight_comul_of_primitive (l : Λ →ₗ[R] R)
    (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : Λ)
    (hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) (u : Λ) :
    ev Λ (l ∘ₗ LinearMap.mulRight R b) (Coalgebra.comul u) =
      l (u * b) • (1 : Λ) - l u • b := by sorry
