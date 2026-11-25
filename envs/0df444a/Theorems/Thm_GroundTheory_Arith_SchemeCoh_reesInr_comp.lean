-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_reesInr_comp
-- name    : GroundTheory.Arith.SchemeCoh.reesInr_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:19.524954+00:00
-- url     : https://prove2.me/theorems/417695a5-c7a1-4744-9f71-5d74ed1e0c71
-- title:
--   Scheme Coh: rees Inr comp
-- statement:
--   The Scheme Coh construction uses the rees Inr comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L86-L91

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
include hV

theorem GroundTheory.Arith.SchemeCoh.reesInr_comp :
    reesInr I V ≫ (reesPolyMap I X).app _ =
      CommRingCat.ofHom (algebraMap (reesAlgebra I) (Polynomial A)) ≫ polyInr I V := by sorry
