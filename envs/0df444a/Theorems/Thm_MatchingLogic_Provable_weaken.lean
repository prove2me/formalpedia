-- Prove2me | Theorems.Thm_MatchingLogic_Provable_weaken
-- name    : MatchingLogic.Provable.weaken
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:50.89725+00:00
-- url     : https://prove2.me/theorems/cff15f3d-b133-4ed3-9f30-769f325d2ca2
-- title:
--   Provable: weaken
-- statement:
--   Provability is monotone in its hypotheses.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L186-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L186-L199

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Provable.weaken {Γ Δ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓΔ : Γ ⊆ Δ) (h : Provable Γ φ) : Provable Δ φ := by sorry
