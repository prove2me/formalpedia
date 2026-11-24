-- Prove2me | Theorems.Thm_GlobalTheory_conductor_prod_fst
-- name    : GlobalTheory.conductor_prod_fst
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:36.585249+00:00
-- url     : https://prove2.me/theorems/c2a70cff-db39-407e-9938-238c3b0b3e90
-- title:
--   Global Theory: conductor prod fst
-- statement:
--   The Global Theory construction uses the conductor prod fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConductorProdFst.lean#L6-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConductorProdFst.lean#L6-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConductorProdFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory

theorem GlobalTheory.conductor_prod_fst (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S]
    (e : S ≃+* R × S') (d : S)
    (hd : ∀ c : FractionRing S, IsIntegral S c →
      ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) :
    ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by sorry
