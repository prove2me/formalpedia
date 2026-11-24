-- Prove2me | Theorems.Thm_GlobalTheory_subst_pair_subst_X
-- name    : GlobalTheory.subst_pair_subst_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:08.314891+00:00
-- url     : https://prove2.me/theorems/0c3d0789-5539-4f8d-962b-ef1970996bc3
-- title:
--   Global Theory: subst pair subst X
-- statement:
--   The Global Theory construction uses the subst pair subst X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SubstTwoVariablesIdentities.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SubstTwoVariablesIdentities.lean#L12-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SubstTwoVariablesIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPowerSeries

theorem GlobalTheory.subst_pair_subst_X {k : Type} [CommRing k] (x : PowerSeries k) (i : Fin 2)
    {a : Fin 2 → PowerSeries k} (ha : HasSubst a) :
    subst a (x.subst (X i : MvPowerSeries (Fin 2) k)) = x.subst (a i) := by sorry
