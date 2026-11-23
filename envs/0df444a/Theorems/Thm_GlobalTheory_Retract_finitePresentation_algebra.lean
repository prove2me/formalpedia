-- Prove2me | Theorems.Thm_GlobalTheory_Retract_finitePresentation_algebra
-- name    : GlobalTheory.Retract.finitePresentation_algebra
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:05.848956+00:00
-- url     : https://prove2.me/theorems/42533c90-3d78-4a3f-8987-6ec23e428017
-- title:
--   Retract: finite Presentation algebra
-- statement:
--   The Retract construction uses the finite Presentation algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L49-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (s : A →ₐ[R] B) (p : B →ₐ[R] A) (h : p.comp s = AlgHom.id R A)
include h

theorem GlobalTheory.Retract.finitePresentation_algebra [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A := by sorry
