-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_reesRingHom_inl
-- name    : GroundTheory.Arith.SchemeCoh.reesRingHom_inl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:11.629618+00:00
-- url     : https://prove2.me/theorems/b8100367-ca2a-4024-97eb-13a69953d0f1
-- title:
--   Scheme Coh: rees Ring Hom inl
-- statement:
--   The Scheme Coh construction uses the rees Ring Hom inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L96-L97

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
noncomputable section
variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {V : X.Opens} (hV : IsAffineOpen V)

theorem GroundTheory.Arith.SchemeCoh.reesRingHom_inl (c : Γ(X, V)) : reesRingHom hV ((reesPr I X).app V c) = Polynomial.C c := by sorry
