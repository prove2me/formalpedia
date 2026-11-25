-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_FixDisc_exists_rat_basis
-- name    : GlobalTheory.DegCnt.FixDisc.exists_rat_basis
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:25.081501+00:00
-- url     : https://prove2.me/theorems/3fc87438-dcab-5e33-98f3-afbee8e4e64a
-- title:
--   Fix Disc: exists rat basis
-- statement:
--   The Fix Disc construction uses the exists rat basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L42-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L42-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.FixDisc.exists_rat_basis [Module ℚ V] [Module.Finite ℚ V] {A : Submodule (𝓞 K) V}
    (hA : Submodule.IsLattice K A) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ V)) ℚ V, A.toAddSubgroup = AddSubgroup.closure (Set.range b) := by sorry
