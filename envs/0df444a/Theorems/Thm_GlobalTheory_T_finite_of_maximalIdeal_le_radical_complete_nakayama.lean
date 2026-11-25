-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_of_maximalIdeal_le_radical_complete_nakayama
-- name    : GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:51.692117+00:00
-- url     : https://prove2.me/theorems/e671ea73-038a-40b9-b191-54988756761b
-- title:
--   T: finite of maximal Ideal le radical complete nakayama
-- statement:
--   The T construction uses the finite of maximal Ideal le radical complete nakayama property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfMaximalIdealLeRadicalCompleteNakayamaStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfMaximalIdealLeRadicalCompleteNakayamaStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfMaximalIdealLeRadicalCompleteNakayama
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfMaximalIdealLeRadicalCompleteNakayamaStatement
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama : ∀ (B R : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ → maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite → ψ.Finite := by sorry
