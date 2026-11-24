-- Prove2me | Theorems.Thm_GlobalTheory_eval_map_mem_maximalIdeal_pow_of_coeff_mem
-- name    : GlobalTheory.eval_map_mem_maximalIdeal_pow_of_coeff_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:39.063855+00:00
-- url     : https://prove2.me/theorems/b00b4d20-3985-42ca-809a-0df6b3ce426b
-- title:
--   Global Theory: eval map mem maximal Ideal pow of coeff mem
-- statement:
--   The Global Theory construction uses the eval map mem maximal Ideal pow of coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HenselRootsCompatible.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HenselRootsCompatible.lean#L21-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HenselRootsCompatible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.eval_map_mem_maximalIdeal_pow_of_coeff_mem {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) (D : Polynomial A)
    (hD : ∀ i, D.coeff i ∈ maximalIdeal A ^ n) (η : V) :
    (D.map α).eval η ∈ maximalIdeal V ^ n := by sorry
