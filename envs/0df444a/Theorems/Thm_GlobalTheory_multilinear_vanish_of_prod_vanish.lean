-- Prove2me | Theorems.Thm_GlobalTheory_multilinear_vanish_of_prod_vanish
-- name    : GlobalTheory.multilinear_vanish_of_prod_vanish
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:12:17.07113+00:00
-- url     : https://prove2.me/theorems/a73308eb-bae3-4604-970f-a44a6868b679
-- title:
--   Global Theory: multilinear vanish of prod vanish
-- statement:
--   The Global Theory construction uses the multilinear vanish of prod vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearVanishOfProdVanish.lean#L125-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearVanishOfProdVanish.lean#L125-L131

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

theorem GlobalTheory.multilinear_vanish_of_prod_vanish {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : MultilinearMap K (fun i => A i) M) {D : Type} (s : Finset D) (c : D → K)
    (f : D → ∀ i, A i)
    (hx : ∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) :
    ∑ d ∈ s, c d • P (f d) = 0 := by sorry
