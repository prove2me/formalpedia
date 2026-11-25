-- Prove2me | Theorems.Thm_GlobalTheory_IndexProd_relIndex_eq_inf_mul_sup
-- name    : GlobalTheory.IndexProd.relIndex_eq_inf_mul_sup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:01:31.401072+00:00
-- url     : https://prove2.me/theorems/10f69b82-0a9e-4261-a109-575cbe018de8
-- title:
--   Index Prod: rel Index eq inf mul sup
-- statement:
--   The Index Prod construction uses the rel Index eq inf mul sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InvVolEqInfMulSupAndMono.lean#L40-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InvVolEqInfMulSupAndMono.lean#L40-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolEqInfMulSupAndMono
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
open GlobalTheory GlobalTheory.IndexProd

theorem GlobalTheory.IndexProd.relIndex_eq_inf_mul_sup {G : Type*} [Group G] {D A M : Subgroup G} (hDA : D ≤ A)
    (h : ∀ s ∈ A, ∀ t ∈ M, s * t * s⁻¹ ∈ M) :
    D.relIndex A = (D ⊓ M).relIndex (A ⊓ M) * (D ⊔ M).relIndex (A ⊔ M) := by sorry
