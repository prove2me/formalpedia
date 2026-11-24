-- Prove2me | Theorems.Thm_Mader_no_split
-- name    : Mader.no_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:52:09.096727+00:00
-- url     : https://prove2.me/theorems/4d747bcd-55b7-4f0d-b32d-de3512835470
-- title:
--   Mader: no split
-- statement:
--   The Mader construction uses the no split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderSteps.lean#L45-L99
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderSteps.lean#L45-L99

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

theorem Mader.no_split [DecidableEq V] {S X U₁ U₂ : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hmin : ∀ S' : Finset V, S'.card < S.card → 2 * k ≤ S'.card →
       (dbl G S' : ℤ) * n ≤ (m : ℤ) * ((S'.card : ℤ) - k))
    (hP : (m : ℤ) * ((S.card : ℤ) - k) < (dbl G S : ℤ) * n)
    (hdeg : ∀ v ∈ S, m < 2 * ndeg G S v * n)
    (hX : X.card ≤ k) (hS : S = U₁ ∪ U₂ ∪ X) (h12 : Disjoint U₁ U₂) (h1X : Disjoint U₁ X)
    (h2X : Disjoint U₂ X) (hne1 : U₁.Nonempty) (hne2 : U₂.Nonempty)
    (hno : ∀ a ∈ U₁, ∀ b ∈ U₂, ¬ G.Adj a b) : False := by sorry
