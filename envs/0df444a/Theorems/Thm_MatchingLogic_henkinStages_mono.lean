-- Prove2me | Theorems.Thm_MatchingLogic_henkinStages_mono
-- name    : MatchingLogic.henkinStages_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:57.971555+00:00
-- url     : https://prove2.me/theorems/9874934c-1c21-4a48-9a65-125c26c7a8ed
-- title:
--   Matching Logic: henkin Stages mono
-- statement:
--   A stage operation that only enlarges represented theories gives a monotone
--   sequence of finite Henkin stages.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L178-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L178-L183

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed

theorem MatchingLogic.henkinStages_mono {α : Type} (stageTheory : List α → Set α)
    (step : List α → α → List α) (enum : Nat → α) (base : List α)
    (hstep : ∀ l phi, stageTheory l ⊆ stageTheory (step l phi)) :
    Monotone (fun n => stageTheory (henkinStages step enum base n)) := by sorry
