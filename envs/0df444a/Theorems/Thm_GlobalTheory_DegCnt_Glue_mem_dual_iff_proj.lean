-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_Glue_mem_dual_iff_proj
-- name    : GlobalTheory.DegCnt.Glue.mem_dual_iff_proj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:25:50.182932+00:00
-- url     : https://prove2.me/theorems/dd523ae1-b24f-54c9-b7a0-9db205752020
-- title:
--   Glue: mem dual iff proj
-- statement:
--   The Glue construction uses the mem dual iff proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUnimodularHermGluingsLe.lean#L111-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUnimodularHermGluingsLe.lean#L111-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Glue
open TensorProduct
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (H : HermSpace K V) {U : Submodule K V} (hc : IsCompl U (perp H U)) {L : Submodule (𝓞 K) V}
  (hU : IsUnimod H L) {p : V →ₗ[K] V} (hp : ∀ v, p v ∈ U) (hq : ∀ v, v - p v ∈ perp H U)
include hc hU hp hq

theorem GlobalTheory.DegCnt.Glue.mem_dual_iff_proj (d : V) : d ∈ dual H (L ⊓ rs (𝓞 K) (perp H U)) ↔ ∃ v ∈ L, v - p v = d := by sorry
