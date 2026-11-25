-- Prove2me | Theorems.Thm_GlobalTheory_WachTie_Laur_co_tw
-- name    : GlobalTheory.WachTie.Laur.co_tw
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:43.096639+00:00
-- url     : https://prove2.me/theorems/1d311622-3339-40c8-8bd9-417ab98b38ae
-- title:
--   Laur: co tw
-- statement:
--   The Laur construction uses the co tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfSumSmul.lean#L133-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfSumSmul.lean#L133-L134

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfSumSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
open GlobalTheory GlobalTheory.WachTie
open GlobalTheory.WachTie.Laur
variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']

theorem GlobalTheory.WachTie.Laur.co_tw (c : L) (g : M →ₗ[L] M') (x : Laur L M) (k : ℤ) :
    co (tw c g x) k = c ^ k • g (co x k) := by sorry

attribute [defeq] GlobalTheory.WachTie.Laur.co_tw
