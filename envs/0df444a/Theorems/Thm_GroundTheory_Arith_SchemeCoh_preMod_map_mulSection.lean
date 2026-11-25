-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_preMod_map_mulSection
-- name    : GroundTheory.Arith.SchemeCoh.preMod_map_mulSection
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:48:35.499832+00:00
-- url     : https://prove2.me/theorems/66fe87a6-8de4-496d-bd48-bf571ed32ce2
-- title:
--   Scheme Coh: pre Mod map mul Section
-- statement:
--   The Scheme Coh construction uses the pre Mod map mul Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SectionTensor.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SectionTensor.lean#L113-L115

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SectionTensor
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct
universe u
noncomputable section
variable {X : Scheme.{u}}
variable (M L : X.Modules) (s : Γ(L, ⊤))

theorem GroundTheory.Arith.SchemeCoh.preMod_map_mulSection :
    (preMod X).map (mulSection M L s) = tensorSection M L s ≫ tensorToSheaf M L := by sorry
