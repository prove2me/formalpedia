-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_sUnits_rank
-- name    : GlobalTheory.QNorm.sUnits_rank
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:04:04.097914+00:00
-- url     : https://prove2.me/theorems/d4bcbd67-8558-4655-abdd-dc301cbdeecb
-- title:
--   QNorm: s Units rank
-- statement:
--   The QNorm construction uses the s Units rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FinrankSUnitsNumberFieldAddOne.lean#L37-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FinrankSUnitsNumberFieldAddOne.lean#L37-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsNumberFieldFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FinrankSUnitsNumberFieldAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.sUnits_rank :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
      Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by sorry
