-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_relIndex_ordBall_succ
-- name    : GlobalTheory.BorelUMod.UpLatIndex.relIndex_ordBall_succ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:01:31.645461+00:00
-- url     : https://prove2.me/theorems/d1cad5b6-02df-4456-85b4-bb9dd0304ff4
-- title:
--   Up Lat Index: rel Index ord Ball succ
-- statement:
--   The Up Lat Index construction uses the rel Index ord Ball succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L32-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L32-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.UpLatIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.BorelUMod.UpLatIndex.relIndex_ordBall_succ {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    (ordBall L (k + 1)).relIndex (ordBall L k) =
      Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring ⧸
        IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) := by sorry
