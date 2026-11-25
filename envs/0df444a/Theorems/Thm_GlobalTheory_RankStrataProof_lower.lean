-- Prove2me | Theorems.Thm_GlobalTheory_RankStrataProof_lower
-- name    : GlobalTheory.RankStrataProof.lower
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:06.986043+00:00
-- url     : https://prove2.me/theorems/b88888ce-f456-52d3-8e18-a76ddbe534b8
-- title:
--   Rank Strata Proof: lower
-- statement:
--   The Rank Strata Proof construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingTopEmb.lean#L131-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingTopEmb.lean#L131-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftColumnsMulVecInjectiveOfRankEqCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RankFiltrationExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingTopEmb
import Theorems.Thm_GlobalTheory_SmGL_InductionContragredient_lower
import Theorems.Thm_GlobalTheory_SmGL_InductionFiniteLength_lower
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.RankStrataProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

theorem GlobalTheory.RankStrataProof.lower (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (z : ℂ) (hz : z + (Fintype.card c : ℂ) / 2 = (Fintype.card b : ℂ) / 2) :
    Nonempty (Representation.Equiv ((omegaOn a b μ {κ}).comp (MonoidHom.inl _ _))
      (ind₂Lower e (extTensor (colRep b e {κ}
        (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2 + (Fintype.card d : ℂ) / 2)))
        (detRep d (μ⁻¹ * absPow k z))))) := by sorry
