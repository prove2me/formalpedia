-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_reesRingHom_inr
-- name    : GroundTheory.Arith.SchemeCoh.reesRingHom_inr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:00.563999+00:00
-- url     : https://prove2.me/theorems/4d65c8cc-ad74-4a5f-8232-2ac4fe12be9b
-- title:
--   Scheme Coh: rees Ring Hom inr
-- statement:
--   The Scheme Coh construction uses the rees Ring Hom inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L99-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L99-L105

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

theorem GroundTheory.Arith.SchemeCoh.reesRingHom_inr (r : reesAlgebra I) :
    reesRingHom hV (reesInr I V r) = (r : Polynomial A).map (algV X V) := by sorry
