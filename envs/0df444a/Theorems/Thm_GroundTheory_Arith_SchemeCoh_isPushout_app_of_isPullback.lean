-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isPushout_app_of_isPullback
-- name    : GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:25.889222+00:00
-- url     : https://prove2.me/theorems/a8e974d4-74bf-4273-a4d3-c36cfbe81152
-- title:
--   Scheme Coh: is Pushout app of is Pullback
-- statement:
--   The Scheme Coh construction uses the is Pushout app of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackGamma.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackGamma.lean#L14-L33

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackGamma
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
variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Z]
    {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout (f.appLE ⊤ V le_top) g.appTop (fst.app V) (snd.appLE ⊤ (fst ⁻¹ᵁ V) le_top) := by sorry
