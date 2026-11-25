-- Prove2me | Theorems.Thm_GlobalTheory_CongIndex_card_hom_quot_smul_top
-- name    : GlobalTheory.CongIndex.card_hom_quot_smul_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:35.17357+00:00
-- url     : https://prove2.me/theorems/fbc9a6d3-b2c9-4041-a73b-ae34a3383a55
-- title:
--   Cong Index: card hom quot smul top
-- statement:
--   The Cong Index construction uses the card hom quot smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexCongruenceSubgroupLeAbsNormPow.lean#L39-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexCongruenceSubgroupLeAbsNormPow.lean#L39-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
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
open GlobalTheory GlobalTheory.CongIndex

theorem GlobalTheory.CongIndex.card_hom_quot_smul_top {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ∧
    Nat.card (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ≤ Nat.card (R ⧸ I) ^ (Module.finrank R N ^ 2) := by sorry
