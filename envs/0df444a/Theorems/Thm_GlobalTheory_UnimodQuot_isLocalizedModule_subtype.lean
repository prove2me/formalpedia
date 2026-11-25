-- Prove2me | Theorems.Thm_GlobalTheory_UnimodQuot_isLocalizedModule_subtype
-- name    : GlobalTheory.UnimodQuot.isLocalizedModule_subtype
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:05.084731+00:00
-- url     : https://prove2.me/theorems/39ef8443-a02c-584b-b92a-e2cba8a75e01
-- title:
--   Unimod Quot: is Localized Module subtype
-- statement:
--   The Unimod Quot construction uses the is Localized Module subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLocalizedModuleSubtype.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLocalizedModuleSubtype.lean#L64-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
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
open GlobalTheory GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V]

theorem GlobalTheory.UnimodQuot.isLocalizedModule_subtype {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by sorry
