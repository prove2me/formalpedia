-- Prove2me | Theorems.Thm_MatchingLogic_cover_sat_iff
-- name    : MatchingLogic.cover_sat_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:49.077882+00:00
-- url     : https://prove2.me/theorems/e0acf764-e9ae-4215-b912-435a0035d56c
-- title:
--   Matching Logic: cover sat iff
-- statement:
--   **Corollary 12**, second half: `N ⊨ ψ` iff `C ⊆ ⟦ψ⟧_M`.
--
--   Note that `star` and `hstar` appear nowhere in the statement, only in the proof
--   (Lemma 11 consumes them).  They are not vestigial: requiring a point outside `C`
--   is how this theorem carries Definition 10's standing assumption `C ≠ M`.  A
--   caller must exhibit one, so Corollary 12 does NOT apply when `C = M` -- which is
--   exactly why Theorem 13 handles that case separately.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Composite.lean#L55-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Composite.lean#L55-L71

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

theorem MatchingLogic.cover_sat_iff (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    {ψ : Pattern S Var} (hψ : Closed ψ) (ρ : Var → M.carrier) :
    (cover M C hne).Sat ψ ↔ C ⊆ M.denote ρ ψ := by sorry
