-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_mul_fst_eq_of_integral_of_conductor
-- name    : GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:36:50.057307+00:00
-- url     : https://prove2.me/theorems/d912e242-135f-415b-a68d-0cce9365b3ad
-- title:
--   T: exists mul fst eq of integral of conductor
-- statement:
--   The T construction uses the exists mul fst eq of integral of conductor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConductorProdFstStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConductorProdFstStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConductorProdFst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConductorProdFstStatement
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

theorem GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor : ∀ (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S] (e : S ≃+* R × S') (d : S), (∀ c : FractionRing S, IsIntegral S c → ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) → ∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by sorry
