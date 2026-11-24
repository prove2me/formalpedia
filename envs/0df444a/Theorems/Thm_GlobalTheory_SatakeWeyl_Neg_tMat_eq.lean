-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Neg_tMat_eq
-- name    : GlobalTheory.SatakeWeyl.Neg.tMat_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:42.058219+00:00
-- url     : https://prove2.me/theorems/90641b71-6216-41d4-a924-3fb690d3b7c5
-- title:
--   Neg: t Mat eq
-- statement:
--   The Neg construction uses the t Mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffLastSignChangeOfLeviReduction.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffLastSignChangeOfLeviReduction.lean#L16-L28

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReduction
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Neg

theorem GlobalTheory.SatakeWeyl.Neg.tMat_eq {L : Type} [Field L] (ϖ : L) {n m : ℕ} (a : Fin m → ℤ) :
    tMat ϖ n m a = Matrix.diagonal fun x => ϖ ^ expo n m (ext a) x := by sorry
