-- Prove2me | Theorems.Thm_MazurReduction_rational_residue_field_equiv
-- name    : MazurReduction.rational_residue_field_equiv
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T10:17:44.637335+00:00
-- url     : https://prove2.me/theorems/2a6b1515-1597-44fd-abd7-970a2ee71d87
-- title:
--   Residue field of the rational p-adic valuation
-- statement:
--   For every prime $p$, let $A_p$ be the valuation ring of the standard multiplicative $p$-adic valuation on the rational numbers. Its residue field is isomorphic to the prime field: $$A_p/\mathfrak m_p\;\cong\;\mathbb F_p.$$ The isomorphism preserves addition, multiplication, zero and one. This identifies generic valuation-ring reduction with the prime-field reduction used in the full Mazur campaign.
-- source:
--   New Mazur campaign proof by Vasily Ilin, October 2026; Mathlib NumberTheory/Padics/PadicNumbers.lean: Rat.padicValuation_le_one_iff, Rat.padicValuation_self; RingTheory/Valuation/ValuationSubring.lean: Valuation.mem_maximalIdeal_iff.

import Mathlib
open WithZero IsLocalRing

theorem MazurReduction.rational_residue_field_equiv (p : ℕ) [Fact p.Prime] :
    Nonempty (IsLocalRing.ResidueField (Rat.padicValuation p).valuationSubring ≃+* ZMod p) := by sorry
