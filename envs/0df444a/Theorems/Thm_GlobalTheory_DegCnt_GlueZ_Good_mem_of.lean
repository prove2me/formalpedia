-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_GlueZ_Good_mem_of
-- name    : GlobalTheory.DegCnt.GlueZ.Good.mem_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:06:42.439567+00:00
-- url     : https://prove2.me/theorems/9d042f22-8ba4-5e9e-84dd-61771a1d8683
-- title:
--   Good: mem of
-- statement:
--   The Good construction uses the mem of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardInnerLatticesWithDefiniteTraceLeNorm.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardInnerLatticesWithDefiniteTraceLeNorm.lean#L37-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardInnerLatticesWithDefiniteTraceLeNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.GlueZ
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {S : Submodule K V} {z : V} {M : Submodule (𝓞 K) V}

theorem GlobalTheory.DegCnt.GlueZ.Good.mem_of (h : Good H S z M) {x : V} (hx : x ∈ S)
    (hB : ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ M := by sorry
