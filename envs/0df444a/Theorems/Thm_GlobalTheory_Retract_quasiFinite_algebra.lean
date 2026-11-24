-- Prove2me | Theorems.Thm_GlobalTheory_Retract_quasiFinite_algebra
-- name    : GlobalTheory.Retract.quasiFinite_algebra
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:43.797669+00:00
-- url     : https://prove2.me/theorems/c89428cc-21d3-4e2d-aa50-54e4696ff790
-- title:
--   Retract: quasi Finite algebra
-- statement:
--   The Retract construction uses the quasi Finite algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L73-L74

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

theorem GlobalTheory.Retract.quasiFinite_algebra [Algebra.QuasiFinite R B] : Algebra.QuasiFinite R A := by sorry
