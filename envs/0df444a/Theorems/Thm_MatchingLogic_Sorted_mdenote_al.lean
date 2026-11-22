-- Prove2me | Theorems.Thm_MatchingLogic_Sorted_mdenote_al
-- name    : MatchingLogic.Sorted.mdenote_al
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:29.975414+00:00
-- url     : https://prove2.me/theorems/5a26c6f2-4821-42d0-8798-9560125b48da
-- title:
--   Sorted: mdenote al
-- statement:
--   The denotation clause for sorted universal quantification.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L136-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L136-L141

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type}

theorem MatchingLogic.Sorted.mdenote_al (M : MModel S) (ρ : MVal M Var) {s : S.Srt}
    (x : Var) (s' : S.Srt) (φ : MPattern S Var s) :
    mdenote M ρ (MPattern.al x s' φ) =
      ⋂ a : M.carrier s', mdenote M (mupdate M ρ s' x a) φ := by sorry
