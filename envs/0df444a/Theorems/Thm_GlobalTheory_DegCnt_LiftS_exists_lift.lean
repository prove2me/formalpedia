-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_LiftS_exists_lift
-- name    : GlobalTheory.DegCnt.LiftS.exists_lift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:31:04.827541+00:00
-- url     : https://prove2.me/theorems/2da7d096-8cf8-5b74-a769-f3f4ef64af6b
-- title:
--   Lift S: exists lift
-- statement:
--   The Lift S construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L615-L778
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L615-L778

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegCnt.LiftS.exists_lift [FiniteDimensional K V] (N : NF H r) (h0 : II N.F N.F' ⊓ N.F.Xa N.j = ⊥)
    (htop : N.Wt ⊔ (V0 N.F N.F' ⊔ N.Ist) = ⊤) (τ : K) (hτ : τ + star τ = 1) (s : V ≃ₗ[K] V)
    (hF : N.F.InN (s : V →ₗ[K] V)) (hF' : N.F'.InN (s : V →ₗ[K] V))
    (hU : ∀ y ∈ uPerp N.F N.F', s y - y ∈ II N.F N.F')
    (hU' : ∀ y ∈ uPerp N.F N.F', s.symm y - y ∈ II N.F N.F') :
    ∃ s' ∈ N.Rs, (∀ y ∈ V0 N.F N.F', s' y = s y) ∧
      ∀ y ∈ N.Ist, s' y = trans H (s N.F.z - N.F.z) N.F.z N.T τ (qI N (s y)) := by sorry
