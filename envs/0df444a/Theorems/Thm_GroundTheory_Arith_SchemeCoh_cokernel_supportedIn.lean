-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_cokernel_supportedIn
-- name    : GroundTheory.Arith.SchemeCoh.cokernel_supportedIn
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:50.264493+00:00
-- url     : https://prove2.me/theorems/68ef271d-ae30-57c2-b829-1afc0a44733a
-- title:
--   Scheme Coh: cokernel supported In
-- statement:
--   The Scheme Coh construction uses the cokernel supported In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/Support.lean#L72-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/Support.lean#L72-L93

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_Support
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {X : Scheme.{u}}
variable {F G : X.Modules} (φ : F ⟶ G) (W : X.Opens)

theorem GroundTheory.Arith.SchemeCoh.cokernel_supportedIn (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (φ.app U)) :
    Scheme.Modules.SupportedIn (cokernel φ) (W : Set X)ᶜ := by sorry
