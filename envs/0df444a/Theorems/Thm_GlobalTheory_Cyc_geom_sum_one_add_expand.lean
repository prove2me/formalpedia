-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_geom_sum_one_add_expand
-- name    : GlobalTheory.Cyc.geom_sum_one_add_expand
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:52:58.678864+00:00
-- url     : https://prove2.me/theorems/d85967e2-40cd-49ca-b2d5-c640bc5c49ae
-- title:
--   Cyc: geom sum one add expand
-- statement:
--   The Cyc construction uses the geom sum one add expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L7-L20

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneOfNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Cyc

theorem GlobalTheory.Cyc.geom_sum_one_add_expand {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∃ z : R, (1 + y) ^ n - 1 = y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by sorry
