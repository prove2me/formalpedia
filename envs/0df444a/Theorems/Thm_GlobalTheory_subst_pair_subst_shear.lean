-- Prove2me | Theorems.Thm_GlobalTheory_subst_pair_subst_shear
-- name    : GlobalTheory.subst_pair_subst_shear
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:18.835812+00:00
-- url     : https://prove2.me/theorems/96a56d2e-587b-4bc8-80ff-5aa17bdf5f09
-- title:
--   Global Theory: subst pair subst shear
-- statement:
--   The Global Theory construction uses the subst pair subst shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SubstTwoVariablesIdentities.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SubstTwoVariablesIdentities.lean#L23-L39

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

theorem GlobalTheory.subst_pair_subst_shear {k : Type} [CommRing k] (h : MvPowerSeries (Fin 2) k)
    {z w : PowerSeries k} (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) :
    subst (![z, w] : Fin 2 → PowerSeries k)
      (subst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) =
      subst (![z, z + w] : Fin 2 → PowerSeries k) h := by sorry
