-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SplitOver_adj
-- name    : GlobalTheory.Mass.SplitOver.adj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:01:28.726834+00:00
-- url     : https://prove2.me/theorems/981a750e-0463-49aa-855a-2db8dfc2c181
-- title:
--   Split Over: adj
-- statement:
--   The Split Over construction uses the adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnimodularOverlatticeCyclicSplitDiscrimina.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnimodularOverlatticeCyclicSplitDiscrimina.lean#L55-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnimodularOverlatticeCyclicSplitDiscrimina
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SplitOver
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [FiniteDimensional K V]

theorem GlobalTheory.Mass.SplitOver.adj (h : V →ₗ⋆[K] V →ₗ[K] K) (r : 𝓞 K) (v w : V) : h v (r • w) = h (cj r • v) w := by sorry
