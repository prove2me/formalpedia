-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBaseChangeAt_of_comp_isOpenImmersion
-- name    : GroundTheory.Arith.SchemeCoh.IsBaseChangeAt.of_comp_isOpenImmersion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:35.902483+00:00
-- url     : https://prove2.me/theorems/34f3fd9b-ea9b-427e-8ac8-491cd1da3203
-- title:
--   Is Base Change At: of comp is Open Immersion
-- statement:
--   The Is Base Change At construction uses the of comp is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L123-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L123-L205

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
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
variable {W T U : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.IsBaseChangeAt.of_comp_isOpenImmersion {f : W ⟶ T} [IsOpenImmersion f] {g : T ⟶ U}
    {N : U.Modules} {O : U.Opens} (hO : g ⁻¹ᵁ O ≤ f.opensRange)
    (h : IsBaseChangeAt (f ≫ g) N O) : IsBaseChangeAt g N O := by sorry
