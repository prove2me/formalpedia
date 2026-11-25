-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_C_mem_reesCoeffRing
-- name    : GroundTheory.Arith.SchemeCoh.C_mem_reesCoeffRing
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:35.662896+00:00
-- url     : https://prove2.me/theorems/f56ea19a-97c8-48c1-b37a-e18a15a65f79
-- title:
--   Scheme Coh: C mem rees Coeff Ring
-- statement:
--   The Scheme Coh construction uses the C mem rees Coeff Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L135-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesRing.lean#L135-L141

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

theorem GroundTheory.Arith.SchemeCoh.C_mem_reesCoeffRing (c : Γ(X, V)) : Polynomial.C c ∈ reesCoeffRing I X V := by sorry
