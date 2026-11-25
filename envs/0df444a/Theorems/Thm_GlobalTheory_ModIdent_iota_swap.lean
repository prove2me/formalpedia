-- Prove2me | Theorems.Thm_GlobalTheory_ModIdent_iota_swap
-- name    : GlobalTheory.ModIdent.iota_swap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:19.319122+00:00
-- url     : https://prove2.me/theorems/076c7535-28a1-4b34-8dc1-bcc983386348
-- title:
--   Mod Ident: iota swap
-- statement:
--   The Mod Ident construction uses the iota swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsHermIsometryGraphModScalarFlagPairIota.lean#L132-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsHermIsometryGraphModScalarFlagPairIota.lean#L132-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsHermIsometryGraphModScalarFlagPairIota
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
open GlobalTheory GlobalTheory.ModIdent
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [NumberField K]

theorem GlobalTheory.ModIdent.iota_swap {F F' : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} {y' y : V}
    (h : (y', y) ∈ iotaGraph F F' Λ (g : 𝓞 K)) : (y, y') ∈ iotaGraph F' F Λ (g : 𝓞 K) := by sorry
