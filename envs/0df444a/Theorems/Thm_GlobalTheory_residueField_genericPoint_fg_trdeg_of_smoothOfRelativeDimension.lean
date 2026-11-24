-- Prove2me | Theorems.Thm_GlobalTheory_residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension
-- name    : GlobalTheory.residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:11.673446+00:00
-- url     : https://prove2.me/theorems/a56c5bfd-53fb-4803-a5b1-00e73e6a8e49
-- title:
--   Global Theory: residue Field generic Point fg trdeg of smooth Of Relative Dimension
-- statement:
--   The Global Theory construction uses the residue Field generic Point fg trdeg of smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsOpenImmersionIsStandardSmoothOfRelativeD.lean#L97-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsOpenImmersionIsStandardSmoothOfRelativeD.lean#L97-L107

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

theorem GlobalTheory.residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ), SmoothOfRelativeDimension d f → ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X), letI : Algebra K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) := (Spec.preimage (X.fromSpecResidueField (hZ.1 : IsIrreducible Z).genericPoint ≫ f)).hom.toAlgebra; (⊤ : IntermediateField K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint)).FG ∧ Algebra.trdeg K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) = d := by sorry
