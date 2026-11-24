-- Prove2me | Theorems.Thm_GlobalTheory_multilinear_vanish_of_prod_vanish_of_agree_off_finset
-- name    : GlobalTheory.multilinear_vanish_of_prod_vanish_of_agree_off_finset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:12:08.97914+00:00
-- url     : https://prove2.me/theorems/3b148e3b-bea3-4770-9ec6-43a18554de7a
-- title:
--   Global Theory: multilinear vanish of prod vanish of agree off finset
-- statement:
--   The Global Theory construction uses the multilinear vanish of prod vanish of agree off finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearVanishOfProdVanish.lean#L7-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearVanishOfProdVanish.lean#L7-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MultilinearVanishOfProdVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Function
open GlobalTheory

theorem GlobalTheory.multilinear_vanish_of_prod_vanish_of_agree_off_finset {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : MultilinearMap K (fun i => A i) M) (S : Finset ι) :
    ∀ {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i),
      (∀ i ∉ S, ∀ d ∈ s, ∀ d' ∈ s, f d i = f d' i) →
      (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) →
      ∑ d ∈ s, c d • P (f d) = 0 := by sorry
