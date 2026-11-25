-- Prove2me | Theorems.Thm_GlobalTheory_LeafCoordWeight_wtGe1_of_ordGe
-- name    : GlobalTheory.LeafCoordWeight.wtGe1_of_ordGe
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:37.940581+00:00
-- url     : https://prove2.me/theorems/0cc49627-0c81-49f1-ba56-f06fef2f63e5
-- title:
--   Leaf Coord Weight: wt Ge1 of ord Ge
-- statement:
--   The Leaf Coord Weight construction uses the wt Ge1 of ord Ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeafCoordinateWeightNonnegOfAdaptedChainData.lean#L92-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeafCoordinateWeightNonnegOfAdaptedChainData.lean#L92-L111

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeafCoordinateWeightNonnegOfAdaptedChainData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (Data Kn s0)
open ReciprocityTheory.PGsh (OrdGe lgSum)
open GlobalTheory GlobalTheory.LeafCoordWeight

theorem GlobalTheory.LeafCoordWeight.wtGe1_of_ordGe {C : Type} [Field C] {V : VF C} {i N : ℕ} {w : ℝ}
    {f : MvPowerSeries (Fin N) C}
    (h : OrdGe V.v (fun _ => 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) f w) :
    WtGe1 V i w f := by sorry
