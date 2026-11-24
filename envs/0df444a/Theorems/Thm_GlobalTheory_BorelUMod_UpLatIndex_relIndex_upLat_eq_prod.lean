-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_relIndex_upLat_eq_prod
-- name    : GlobalTheory.BorelUMod.UpLatIndex.relIndex_upLat_eq_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:01:46.800431+00:00
-- url     : https://prove2.me/theorems/dbb15820-037b-431f-89bd-074087a4ca80
-- title:
--   Up Lat Index: rel Index up Lat eq prod
-- statement:
--   The Up Lat Index construction uses the rel Index up Lat eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L92-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L92-L117

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

theorem GlobalTheory.BorelUMod.UpLatIndex.relIndex_upLat_eq_prod {n : ℕ} (c C : Fin n → Fin n → ℤ) :
    (upLat L C).relIndex (upLat L c) =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (ordBall L (C p.1.1 p.1.2)).relIndex (ordBall L (c p.1.1 p.1.2)) := by sorry
