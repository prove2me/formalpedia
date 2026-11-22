-- Prove2me | Theorems.Thm_MatchingLogic_Sorted_satSetHet_homogeneous
-- name    : MatchingLogic.Sorted.satSetHet_homogeneous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:31.975917+00:00
-- url     : https://prove2.me/theorems/6533ea25-e689-4d1b-916b-253137ad8464
-- title:
--   Sorted: sat Set Het homogeneous
-- statement:
--   The homogeneous notion is the heterogeneous one restricted to a single
--   sort.  Without this the restriction in `SatSet` would be silent, and an audit
--   flagged exactly that.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L175-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L175-L183

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

theorem MatchingLogic.Sorted.satSetHet_homogeneous (M : MModel S) {s : S.Srt}
    (Γ : Set (MPattern S Var s)) :
    M.SatSet Γ ↔ M.SatSetHet {p | ∃ γ ∈ Γ, p = ⟨s, γ⟩} := by sorry
