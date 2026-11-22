-- Prove2me | Theorems.Thm_MatchingLogic_locConsistent_insert_captureAvoidingWitness
-- name    : MatchingLogic.locConsistent_insert_captureAvoidingWitness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:00.23369+00:00
-- url     : https://prove2.me/theorems/19bf3d2d-88ee-4e70-be6b-77fe00f17088
-- title:
--   Matching Logic: loc Consistent insert capture Avoiding Witness
-- statement:
--   Adding one fresh Henkin implication is conservative for local
--   consistency.  This is the proof-theoretic heart of the witnessed extension.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L137-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L137-L161

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

theorem MatchingLogic.locConsistent_insert_captureAvoidingWitness
    {Gamma : Set (Pattern S Nat)} {x y : Nat} {p : Pattern S Nat}
    (hGamma : LocConsistent Gamma)
    (hyGamma : ∀ q ∈ Gamma, y ∉ FV q)
    (hyp : y ∉ p.allVars) :
    LocConsistent
      (insert (.imp (.ex x p) (Pattern.captureAvoidingSubst x y p)) Gamma) := by sorry
