-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isPushout_reesPoly
-- name    : GroundTheory.Arith.SchemeCoh.isPushout_reesPoly
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:58.364886+00:00
-- url     : https://prove2.me/theorems/60567d60-c983-47f1-92fc-b332a0f833fb
-- title:
--   Scheme Coh: is Pushout rees Poly
-- statement:
--   The Scheme Coh construction uses the is Pushout rees Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesScheme.lean#L96-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesScheme.lean#L96-L109

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackGamma
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
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
variable {V : X.Opens} (hV : IsAffineOpen V)
include hV

theorem GroundTheory.Arith.SchemeCoh.isPushout_reesPoly :
    IsPushout (CommRingCat.ofHom (algV X V)) (CommRingCat.ofHom (Polynomial.C))
      ((reesPr I X).app V ≫ (reesPolyMap I X).app _) (polyInr I V) := by sorry
