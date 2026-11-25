-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_map_mem_reesCoeffRing
-- name    : GroundTheory.Arith.SchemeCoh.map_mem_reesCoeffRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:12.612108+00:00
-- url     : https://prove2.me/theorems/5990366f-2433-45dd-8dcd-dcccf594496f
-- title:
--   Scheme Coh: map mem rees Coeff Ring
-- statement:
--   The Scheme Coh construction uses the map mem rees Coeff Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L143-L147

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

theorem GroundTheory.Arith.SchemeCoh.map_mem_reesCoeffRing (r : reesAlgebra I) :
    (r : Polynomial A).map (algV X V) ∈ reesCoeffRing I X V := by sorry
