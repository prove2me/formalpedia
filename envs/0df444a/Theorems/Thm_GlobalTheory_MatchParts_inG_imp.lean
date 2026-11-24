-- Prove2me | Theorems.Thm_GlobalTheory_MatchParts_inG_imp
-- name    : GlobalTheory.MatchParts.inG_imp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:58.573355+00:00
-- url     : https://prove2.me/theorems/523a1161-812d-4d5c-858c-0c1e572617ec
-- title:
--   Match Parts: in G imp
-- statement:
--   The Match Parts construction uses the in G imp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L246-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L246-L255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.MatchParts
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N N' : NumD C} {q : QuadraticMap ℤ N.X ℝ} {q' : QuadraticMap ℤ N'.X ℝ} {n g g' : ℕ}

theorem GlobalTheory.MatchParts.inG_imp (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) (j : ℕ) (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j))
    (h : μ.r _ p p') (hp : N.InG p) : N'.InG p' := by sorry
