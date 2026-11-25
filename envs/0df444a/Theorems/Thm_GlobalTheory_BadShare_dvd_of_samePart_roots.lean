-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_dvd_of_samePart_roots
-- name    : GlobalTheory.BadShare.dvd_of_samePart_roots
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:13:51.505196+00:00
-- url     : https://prove2.me/theorems/c86d9e4c-5639-4e0f-9742-0804e04ba088
-- title:
--   Bad Share: dvd of same Part roots
-- statement:
--   The Bad Share construction uses the dvd of same Part roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusMassSamePartOneFactorLe.lean#L30-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusMassSamePartOneFactorLe.lean#L30-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassUnionBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassSamePartOneFactorLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare

theorem GlobalTheory.BadShare.dvd_of_samePart_roots {g : ℕ} [Fact g.Prime] {P : (ZMod g)[X]} (hP : Irreducible P) (h0 : P.coeff 0 ≠ 0)
    {l : ℕ} (hl : l.Prime) {x y : AlgebraicClosure (ZMod g)} (hx : x ∈ P.aroots (AlgebraicClosure (ZMod g)))
    (hy : y ∈ P.aroots (AlgebraicClosure (ZMod g))) (hxy : x ≠ y) (hs : SamePart l x y) :
    2 ≤ P.natDegree ∧ l ∣ g ^ P.natDegree - 1 := by sorry
