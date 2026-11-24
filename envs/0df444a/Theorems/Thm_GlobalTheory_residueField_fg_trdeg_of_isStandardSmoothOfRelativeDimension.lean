-- Prove2me | Theorems.Thm_GlobalTheory_residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension
-- name    : GlobalTheory.residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:14.612364+00:00
-- url     : https://prove2.me/theorems/73157860-b121-4863-a8ee-21355974437b
-- title:
--   Global Theory: residue Field fg trdeg of is Standard Smooth Of Relative Dimension
-- statement:
--   The Global Theory construction uses the residue Field fg trdeg of is Standard Smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsOpenImmersionIsStandardSmoothOfRelativeD.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsOpenImmersionIsStandardSmoothOfRelativeD.lean#L7-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIsOpenImmersionIsStandardSmoothOfRelativeD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory

theorem GlobalTheory.residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [Algebra K B] (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K B]
    (p : Ideal B) [p.IsPrime] (hp : ∀ q : Ideal B, q.IsPrime → q ≤ p → q = p) :
    Algebra.EssFiniteType K p.ResidueField ∧ Algebra.trdeg K p.ResidueField = d := by sorry
