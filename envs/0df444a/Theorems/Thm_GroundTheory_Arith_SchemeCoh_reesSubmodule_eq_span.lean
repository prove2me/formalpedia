-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_reesSubmodule_eq_span
-- name    : GroundTheory.Arith.SchemeCoh.reesSubmodule_eq_span
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:00.739358+00:00
-- url     : https://prove2.me/theorems/3b1a73b3-d5de-4e47-9043-699cec2b7795
-- title:
--   Scheme Coh: rees Submodule eq span
-- statement:
--   The Scheme Coh construction uses the rees Submodule eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesSubmodule.lean#L49-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesSubmodule.lean#L49-L82

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
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
open Polynomial
universe u v w
variable {A : Type u} [CommRing A] (I : Ideal A)
variable (M : Type v) [AddCommGroup M] [Module A M]
variable {I M}
variable (I M)

theorem GroundTheory.Arith.SchemeCoh.reesSubmodule_eq_span :
    reesSubmodule I M =
      Submodule.span (reesAlgebra I) (Set.range (PolynomialModule.single A 0 : M → _)) := by sorry
