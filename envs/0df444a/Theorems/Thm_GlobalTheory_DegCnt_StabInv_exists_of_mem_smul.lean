-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_StabInv_exists_of_mem_smul
-- name    : GlobalTheory.DegCnt.StabInv.exists_of_mem_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:30:13.943604+00:00
-- url     : https://prove2.me/theorems/55096cb5-c7e9-528c-9230-9da1a12569a2
-- title:
--   Stab Inv: exists of mem smul
-- statement:
--   The Stab Inv construction uses the exists of mem smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommonUnipotentStabiliserPreservesTermsAndDatum.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommonUnipotentStabiliserPreservesTermsAndDatum.lean#L99-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [StarRing K]

theorem GlobalTheory.DegCnt.StabInv.exists_of_mem_smul {s : V ≃ₗ[K] V} {Λ : Submodule (𝓞 K) V} {x : V} (hx : x ∈ s • Λ) :
    ∃ y ∈ Λ, s y = x := by sorry
