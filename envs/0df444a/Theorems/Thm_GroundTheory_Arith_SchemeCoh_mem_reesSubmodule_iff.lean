-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_reesSubmodule_iff
-- name    : GroundTheory.Arith.SchemeCoh.mem_reesSubmodule_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:08.559584+00:00
-- url     : https://prove2.me/theorems/614b2f3b-7fbc-50db-b670-11195a0f6fb8
-- title:
--   Scheme Coh: mem rees Submodule iff
-- statement:
--   The Scheme Coh construction uses the mem rees Submodule iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesSubmodule.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesSubmodule.lean#L35-L36

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

theorem GroundTheory.Arith.SchemeCoh.mem_reesSubmodule_iff {p : PolynomialModule A M} :
    p ∈ reesSubmodule I M ↔ ∀ n, p.coeff n ∈ I ^ n • (⊤ : Submodule A M) := by sorry
