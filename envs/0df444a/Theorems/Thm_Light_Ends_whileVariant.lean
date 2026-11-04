-- Prove2me | Theorems.Thm_Light_Ends_whileVariant
-- name    : Light.Ends.whileVariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:44.695826+00:00
-- url     : https://prove2.me/theorems/87674d75-b56c-4849-ad23-5c9e9dd3f720
-- title:
--   Ends: while Variant
-- statement:
--   Loops whose number of rounds depends on the data.  I is the invariant, m a quantity that every
--   round decreases, and b bounds the cost of a round.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L172-L199
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L172-L199

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
public import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.whileVariant {σ c s T} {Q : State → Prop} (I : State → Prop) (m : State → ℕ) (b : ℕ)
    (hI : I σ) (hsafe : ∀ σ, I σ → c.Safe lim σ)
    (hs : ∀ σ, I σ → c.Holds σ → Ends lim P d s σ b fun σ' => I σ' ∧ m σ' < m σ)
    (hn : ∀ σ, I σ → ¬ c.Holds σ → Q σ) (hT : m σ * (c.cost + 1 + b) + (c.cost + 1) ≤ T) :
    Ends lim P d (.while c s) σ T Q := by sorry
