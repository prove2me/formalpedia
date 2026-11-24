-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isIso_morphismRestrict_of_le
-- name    : GroundTheory.Arith.SchemeCoh.isIso_morphismRestrict_of_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:47.4807+00:00
-- url     : https://prove2.me/theorems/bdf419c4-9ef0-4b02-a4c6-1152777f791a
-- title:
--   Scheme Coh: is Iso morphism Restrict of le
-- statement:
--   The Scheme Coh construction uses the is Iso morphism Restrict of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/RestrictIso.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/RestrictIso.lean#L14-L27

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictIso
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
universe u
noncomputable section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem GroundTheory.Arith.SchemeCoh.isIso_morphismRestrict_of_le {U U' : Y.Opens} (h : U' ≤ U) [IsIso (f ∣_ U)] :
    IsIso (f ∣_ U') := by sorry
