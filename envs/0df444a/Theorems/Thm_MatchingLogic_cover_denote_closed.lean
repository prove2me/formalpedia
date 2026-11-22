-- Prove2me | Theorems.Thm_MatchingLogic_cover_denote_closed
-- name    : MatchingLogic.cover_denote_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:48.398158+00:00
-- url     : https://prove2.me/theorems/0fee7c77-8a69-4ace-83c7-972e86d0ba8e
-- title:
--   Matching Logic: cover denote closed
-- statement:
--   **Corollary 12.**  For closed `ψ`, `⟦ψ⟧_N = (⟦ψ⟧_M ∩ C) × {0,1}`.
--   The `∩ C` and the `× {0,1}` are both absorbed by the carrier `↥C × Bool`: the
--   statement says a point of `N` lies in `⟦ψ⟧_N` exactly when its underlying
--   point of `C` lies in `⟦ψ⟧_M`, whichever copy it is in.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Composite.lean#L40-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Composite.lean#L40-L46

module
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Definitions.Def_LeanPool_MatchingLogic_Composite
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
variable (M : Model S) (C : Set M.carrier)

theorem MatchingLogic.cover_denote_closed (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    {ψ : Pattern S Var} (hψ : Closed ψ)
    (ν : Var → (C × Bool)) (ρ : Var → M.carrier) (p : C × Bool) :
    p ∈ (cover M C hne).denote ν ψ ↔ (p.1 : M.carrier) ∈ M.denote ρ ψ := by sorry
