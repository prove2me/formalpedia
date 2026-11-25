-- Prove2me | Theorems.Thm_GlobalTheory_LeafCoordWeight_weight_nonneg
-- name    : GlobalTheory.LeafCoordWeight.weight_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:46:47.966604+00:00
-- url     : https://prove2.me/theorems/334f9f7a-10b5-46c3-93fa-706406811c73
-- title:
--   Leaf Coord Weight: weight nonneg
-- statement:
--   The Leaf Coord Weight construction uses the weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeafCoordinateWeightNonnegOfAdaptedChainData.lean#L113-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeafCoordinateWeightNonnegOfAdaptedChainData.lean#L113-L139

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

theorem GlobalTheory.LeafCoordWeight.weight_nonneg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ c, WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (t c)) := by sorry
