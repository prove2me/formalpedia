-- Prove2me | Theorems.Thm_GlobalTheory_HeightZeroCompare_gaussAbs_eq
-- name    : GlobalTheory.HeightZeroCompare.gaussAbs_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:14.734041+00:00
-- url     : https://prove2.me/theorems/9dd75084-69c6-4a2f-81aa-7488cc723796
-- title:
--   Height Zero Compare: gauss Abs eq
-- statement:
--   The Height Zero Compare construction uses the gauss Abs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SjIffJensenInequality.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SjIffJensenInequality.lean#L13-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SphereBlockLogMean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SjIffJensenInequality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.HeightZeroCompare
open ReciprocityTheory.MultiplicativeHeights GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure

theorem GlobalTheory.HeightZeroCompare.gaussAbs_eq {K : Type} [Field K] [NumberField K] {ι : Type} (w : FinitePlace K)
    (f : MvPolynomial ι K) : gaussAbs w f = gaussAbsValue w f := by sorry
