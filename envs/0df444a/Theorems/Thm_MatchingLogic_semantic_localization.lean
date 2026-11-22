-- Prove2me | Theorems.Thm_MatchingLogic_semantic_localization
-- name    : MatchingLogic.semantic_localization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:22.920463+00:00
-- url     : https://prove2.me/theorems/dcfe3d61-d6e0-4aa8-bde8-fdb63fafd4a8
-- title:
--   Matching Logic: semantic localization
-- statement:
--   **Theorem 13 (paper-facing statement).**  The paper assumes the conclusion
--   closed globally; the mechanized proof above shows that assumption is unused.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Composite.lean#L151-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Composite.lean#L151-L154

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

theorem MatchingLogic.semantic_localization {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (_hφ : Closed φ) :
    GlobalCons Γ φ ↔ LocalCons (localize Γ) φ := by sorry
