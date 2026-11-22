-- Prove2me | Theorems.Thm_MatchingLogic_canonicalExistence_zero
-- name    : MatchingLogic.canonicalExistence_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:32.503709+00:00
-- url     : https://prove2.me/theorems/2cf19e31-be7d-48f5-bf6f-993f40b838d5
-- title:
--   Matching Logic: canonical Existence zero
-- statement:
--   The arity-zero case of the canonical Existence Lemma.  It is stated
--   separately because the tuple of component worlds is genuinely empty, and the
--   universal clause in `canonicalInterp` reduces exactly to membership of the
--   constant application in the output MCS.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L277-L294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L277-L294

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section

theorem MatchingLogic.canonicalExistence_zero
    {sigma : S.Sym} {Gamma : CanonicalCarrier S}
    {phi : Fin (S.arity sigma) → Pattern S Nat}
    (harity : S.arity sigma = 0)
    (happ : Pattern.app sigma phi ∈ Gamma.val) :
    ∃ components : Fin (S.arity sigma) → CanonicalCarrier S,
      (∀ i, phi i ∈ (components i).val) ∧
        Gamma ∈ canonicalInterp sigma components := by sorry
