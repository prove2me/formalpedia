-- Prove2me | Theorems.Thm_GlobalTheory_T_effCartier_comap_of_isIso_restrict_open
-- name    : GlobalTheory.T.effCartier_comap_of_isIso_restrict_open
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:16:28.766682+00:00
-- url     : https://prove2.me/theorems/5697e6be-48d4-4a3c-83aa-42e2e154001d
-- title:
--   T: eff Cartier comap of is Iso restrict open
-- statement:
--   The T construction uses the eff Cartier comap of is Iso restrict open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EffCartierComapOfIsIsoRestrictOpenStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EffCartierComapOfIsIsoRestrictOpenStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EffCartierComapOfIsIsoRestrictOpen
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EffCartierComapOfIsIsoRestrictOpenStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.effCartier_comap_of_isIso_restrict_open : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by sorry
