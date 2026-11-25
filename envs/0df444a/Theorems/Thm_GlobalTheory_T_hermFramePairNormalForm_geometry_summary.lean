-- Prove2me | Theorems.Thm_GlobalTheory_T_hermFramePairNormalForm_geometry_summary
-- name    : GlobalTheory.T.hermFramePairNormalForm_geometry_summary
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:26:52.831431+00:00
-- url     : https://prove2.me/theorems/04d7555f-dc67-4571-a591-7689987973a9
-- title:
--   T: herm Frame Pair Normal Form geometry summary
-- statement:
--   The T construction uses the herm Frame Pair Normal Form geometry summary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummaryStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummaryStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermFramePairNormalForm_geometry_summary : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), NFFull N.F N.F' N.j N.j_le N.c ∧ IsLift N.F N.F' N.Wt ∧ IsCompl N.Wt N.Pi ∧ Module.finrank K N.Wt + 2 * r + 1 = Module.finrank K V ∧ N.Wn = N.Wt ⊔ Submodule.span K {N.F.z} ∧ uPerp N.F N.F' = N.Wn ⊔ II N.F N.F' ∧ wSp N.F N.F' = N.Wt ⊔ II N.F N.F' ∧ wSp N.F' N.F = wSp N.F N.F' ∧ GlobalTheory.Mass.PD (GlobalTheory.Mass.hRes H.B.flip N.Wt) ∧ 1 ≤ N.T ∧ N.nD N.j ≠ 0 ∧ N.Pi = V0 N.F N.F' ⊔ N.Ist := by sorry
