-- Prove2me | Theorems.Thm_GlobalTheory_T_pDivGroup_omega_noPTorsion_of_cotangent_injective
-- name    : GlobalTheory.T.pDivGroup_omega_noPTorsion_of_cotangent_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:42.086944+00:00
-- url     : https://prove2.me/theorems/5e5a3c09-9323-592b-9b3c-4d1d4831912a
-- title:
--   T: p Div Group omega no PTorsion of cotangent injective
-- statement:
--   The T construction uses the p Div Group omega no PTorsion of cotangent injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupOmegaNoPTorsionOfCotangentInjectiveStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupOmegaNoPTorsionOfCotangentInjectiveStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupOmegaNoPTorsionOfCotangentInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupOmegaNoPTorsionOfCotangentInjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pDivGroup_omega_noPTorsion_of_cotangent_injective : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R), (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) → ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by sorry
