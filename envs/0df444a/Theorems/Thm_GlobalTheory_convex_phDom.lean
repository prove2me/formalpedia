-- Prove2me | Theorems.Thm_GlobalTheory_convex_phDom
-- name    : GlobalTheory.convex_phDom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:04.322935+00:00
-- url     : https://prove2.me/theorems/1697d683-b6aa-4bd6-ad2f-20578f52689d
-- title:
--   Global Theory: convex ph Dom
-- statement:
--   The Global Theory construction uses the convex ph Dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine.lean#L82-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
variable {g : ℕ}
open Complex Matrix
variable {g : ℕ}

theorem GlobalTheory.convex_phDom (g : ℕ) : Convex ℝ (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g) := by sorry
