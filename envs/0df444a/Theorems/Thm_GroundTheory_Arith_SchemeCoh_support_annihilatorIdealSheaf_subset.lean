-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_support_annihilatorIdealSheaf_subset
-- name    : GroundTheory.Arith.SchemeCoh.support_annihilatorIdealSheaf_subset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:48:38.829855+00:00
-- url     : https://prove2.me/theorems/763eb049-33cd-4075-b3e3-3ca2e5a983d1
-- title:
--   Scheme Coh: support annihilator Ideal Sheaf subset
-- statement:
--   The Scheme Coh construction uses the support annihilator Ideal Sheaf subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/Annihilator.lean#L79-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/Annihilator.lean#L79-L99

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_Support
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_Annihilator
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

theorem GroundTheory.Arith.SchemeCoh.support_annihilatorIdealSheaf_subset (F : X.Modules) (hF : IsCoherent F) {T : Set X}
    (hT : IsClosed T) (hFT : Scheme.Modules.SupportedIn F T) :
    ((annihilatorIdealSheaf F hF).support : Set X) ⊆ T := by sorry
