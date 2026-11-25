-- Prove2me | Theorems.Thm_GlobalTheory_effCartier_comap_of_isIso_restrict
-- name    : GlobalTheory.effCartier_comap_of_isIso_restrict
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:50:38.829619+00:00
-- url     : https://prove2.me/theorems/dc98c8d9-037b-490a-b743-d3f85672e707
-- title:
--   Global Theory: eff Cartier comap of is Iso restrict
-- statement:
--   The Global Theory construction uses the eff Cartier comap of is Iso restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EffCartierComapOfIsIsoRestrictOpen.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EffCartierComapOfIsIsoRestrictOpen.lean#L9-L17

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EffCartierComapOfIsIsoRestrictOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory

theorem GlobalTheory.effCartier_comap_of_isIso_restrict : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by sorry
