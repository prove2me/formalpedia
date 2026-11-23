-- Prove2me | Theorems.Thm_GlobalTheory_Retract_formallyUnramified_algebra
-- name    : GlobalTheory.Retract.formallyUnramified_algebra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:32.988683+00:00
-- url     : https://prove2.me/theorems/f3b6767f-600e-4d71-ad31-338865f17e9a
-- title:
--   Retract: formally Unramified algebra
-- statement:
--   The Retract construction uses the formally Unramified algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L59-L61

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

theorem GlobalTheory.Retract.formallyUnramified_algebra [Algebra.FormallyUnramified R B] :
    Algebra.FormallyUnramified R A := by sorry
