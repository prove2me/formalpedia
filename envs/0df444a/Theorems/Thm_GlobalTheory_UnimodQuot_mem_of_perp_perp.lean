-- Prove2me | Theorems.Thm_GlobalTheory_UnimodQuot_mem_of_perp_perp
-- name    : GlobalTheory.UnimodQuot.mem_of_perp_perp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:37.008132+00:00
-- url     : https://prove2.me/theorems/d13e41f4-5ce5-4905-ac76-75b55bd419ec
-- title:
--   Unimod Quot: mem of perp perp
-- statement:
--   The Unimod Quot construction uses the mem of perp perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLocalizedModuleSubtype.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLocalizedModuleSubtype.lean#L25-L38

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

theorem GlobalTheory.UnimodQuot.mem_of_perp_perp (H : HermSpace K V) (I : Submodule K V) {v : V}
    (hv : ∀ x ∈ perp H I, H.B x v = 0) : v ∈ I := by sorry
