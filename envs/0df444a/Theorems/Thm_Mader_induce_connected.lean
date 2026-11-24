-- Prove2me | Theorems.Thm_Mader_induce_connected
-- name    : Mader.induce_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:52:02.766988+00:00
-- url     : https://prove2.me/theorems/cabaa1a3-3c50-455f-b188-86cfd3be137b
-- title:
--   Mader: induce connected
-- statement:
--   The Mader construction uses the induce connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderSteps.lean#L138-L205
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderSteps.lean#L138-L205

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
public import Definitions.Def_MaderLib_MaderSteps
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*} (G : SimpleGraph V)

theorem Mader.induce_connected {S : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hmin : ∀ S' : Finset V, S'.card < S.card → 2 * k ≤ S'.card →
       (dbl G S' : ℤ) * n ≤ (m : ℤ) * ((S'.card : ℤ) - k))
    (hP : (m : ℤ) * ((S.card : ℤ) - k) < (dbl G S : ℤ) * n)
    (hdeg : ∀ v ∈ S, m < 2 * ndeg G S v * n)
    (hbig : k + 1 < S.card) (T : Set (S : Set V)) (hT : T.ncard < k + 1) :
    ((G.induce (S : Set V)).induce Tᶜ).Connected := by sorry
