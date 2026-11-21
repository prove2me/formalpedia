-- Prove2me | Theorems.Thm_JardenShami_le_mk_lev_of_splitting
-- name    : JardenShami.le_mk_lev_of_splitting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:24.177176+00:00
-- url     : https://prove2.me/theorems/dfefd39b-22ae-4bc1-8940-bcd95dd9d3b8
-- title:
--   Jarden Shami: le mk lev of splitting
-- statement:
--   AUX: not in paper. The diagonal construction in the proof of Claim 7.9, in a general form.
--   Let `α` be a level such that every node of smaller height has an extension in `Lev_α(T)`, and
--   such that fewer than `ρ` ordinals below `α` are bounded below `α`. If for every `q ∈ [α₀, α)` some
--   `a ∈ Lev_q(T)` has two distinct extensions `b, c` of the same height `< α`, then
--   `|Lev_α(T)| ≥ ρ`. (The paper builds `d_i ∈ Lev_α(T)`, `i < λ`, by induction.)
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L501-L608
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L501-L608

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.le_mk_lev_of_splitting {T : Type w} [PartialOrder T] [IsTree T] {ρ : Cardinal.{w}}
    {α α₀ : Ordinal.{w}} (hext : ∀ x : T, ht x < α → ∃ y ∈ Lev T α, x < y)
    (hbd : ∀ (ι : Type w) (f : ι → Ordinal.{w}), #ι < ρ → (∀ i, f i < α) →
      ∃ q < α, ∀ i, f i ≤ q)
    (hα₀ : α₀ < α)
    (hsplit : ∀ q : Ordinal.{w}, α₀ ≤ q → q < α → ∃ a b c : T, ht a = q ∧ q < ht b ∧
      ht b < α ∧ ht c = ht b ∧ a < b ∧ a < c ∧ b ≠ c) :
    ρ ≤ #(Lev T α) := by sorry
