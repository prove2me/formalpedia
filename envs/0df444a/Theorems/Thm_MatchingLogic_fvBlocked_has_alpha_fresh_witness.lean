-- Prove2me | Theorems.Thm_MatchingLogic_fvBlocked_has_alpha_fresh_witness
-- name    : MatchingLogic.fvBlocked_has_alpha_fresh_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:51.545796+00:00
-- url     : https://prove2.me/theorems/5ba09d8c-be38-4601-9e1f-88e3e7e32315
-- title:
--   Matching Logic: fv Blocked has alpha fresh witness
-- statement:
--   The candidate from the probe has a proof-theoretic alpha-equivalent,
--   vacuously quantified representative.  Thus it is not a counterexample to the
--   alpha-relaxed condition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L82-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L82-L100

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section

theorem MatchingLogic.fvBlocked_has_alpha_fresh_witness :
    ∃ (x' : Nat) (p' : Pattern WitnessCollapseSig Nat) (y : Nat),
      Pattern.AlphaEq
        (.ex 1 (Pattern.and (.var 1) (.var 0))) (.ex x' p') ∧
      y ∉ p'.allVars ∧
      Pattern.imp (.ex x' p')
        (Pattern.captureAvoidingSubst x' y p') ∈ witnessCollapseTheory := by sorry
