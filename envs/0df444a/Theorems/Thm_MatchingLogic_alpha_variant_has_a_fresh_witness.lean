-- Prove2me | Theorems.Thm_MatchingLogic_alpha_variant_has_a_fresh_witness
-- name    : MatchingLogic.alpha_variant_has_a_fresh_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:41.701306+00:00
-- url     : https://prove2.me/theorems/92ba1478-e9c4-4c47-966e-c10474507c6a
-- title:
--   Matching Logic: alpha variant has a fresh witness
-- statement:
--   **The failure is not stable under α-renaming.**
--
--   `∃0. var 0` has no fresh witness above: the only variable naming the witnessing
--   element is `0`, and `0` occurs in the body, so freshness over `allVars` rules it
--   out.  Its α-variant `∃1. var 1` is a different raw pattern with the same
--   meaning, and for it the name `0` *is* fresh — so a fresh witness exists.
--
--   This locates ONE cause of the phenomenon: on raw named syntax the choice of
--   bound name can exhaust the supply of usable witnesses, and choosing another
--   representative of the same α-class restores it.
--
--   It does NOT show that α is the whole story, and an earlier version of this
--   docstring said it was.  `AlphaFreshWitnessed.lean` refutes that: there is an MCS
--   that is `Witnessed` and fails the α-RELAXED condition too, so quotienting by α
--   would not remove the need for the stronger invariant.  What does remove it is an
--   infinite supply of usable witnesses — see `WitnessSupply.lean`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessedCollapse.lean#L184-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessedCollapse.lean#L184-L192

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section
variable {S : Signature}

theorem MatchingLogic.alpha_variant_has_a_fresh_witness :
    ∃ y : Nat, y ∉ (Pattern.var 1 : Pattern WitnessCollapseSig Nat).allVars ∧
      (Pattern.imp (.ex 1 (.var 1))
        (Pattern.captureAvoidingSubst 1 y (.var 1))) ∈ witnessCollapseTheory := by sorry
