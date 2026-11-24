-- Prove2me | Theorems.Thm_GlobalTheory_residueField_fg_trdeg_of_smoothOfRelativeDimension
-- name    : GlobalTheory.residueField_fg_trdeg_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:14.928868+00:00
-- url     : https://prove2.me/theorems/8b20e726-ea59-406b-a523-572843aa2286
-- title:
--   Global Theory: residue Field fg trdeg of smooth Of Relative Dimension
-- statement:
--   The Global Theory construction uses the residue Field fg trdeg of smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsOpenImmersionIsStandardSmoothOfRelativeD.lean#L63-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsOpenImmersionIsStandardSmoothOfRelativeD.lean#L63-L95

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

theorem GlobalTheory.residueField_fg_trdeg_of_smoothOfRelativeDimension {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) (hx : ∀ y : X, y ⤳ x → y = x) :
    letI : Algebra K (X.residueField x) :=
      (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    (⊤ : IntermediateField K (X.residueField x)).FG ∧ Algebra.trdeg K (X.residueField x) = d := by sorry
