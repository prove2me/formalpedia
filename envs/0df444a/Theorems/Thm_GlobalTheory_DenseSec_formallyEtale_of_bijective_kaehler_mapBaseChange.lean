-- Prove2me | Theorems.Thm_GlobalTheory_DenseSec_formallyEtale_of_bijective_kaehler_mapBaseChange
-- name    : GlobalTheory.DenseSec.formallyEtale_of_bijective_kaehler_mapBaseChange
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:25.171796+00:00
-- url     : https://prove2.me/theorems/8b7ae153-50f5-447d-abdc-42ed88afa58f
-- title:
--   Dense Sec: formally Etale of bijective kaehler map Base Change
-- statement:
--   The Dense Sec construction uses the formally Etale of bijective kaehler map Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEtaleChartSmoothAlgebraLocalPoint.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEtaleChartSmoothAlgebraLocalPoint.lean#L11-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEtaleChartSmoothAlgebraLocalPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.DenseSec
open KaehlerDifferential
open scoped TensorProduct

theorem GlobalTheory.DenseSec.formallyEtale_of_bijective_kaehler_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Algebra.FormallySmooth R B]
    (h : Function.Bijective (mapBaseChange R P B)) : Algebra.FormallyEtale P B := by sorry
