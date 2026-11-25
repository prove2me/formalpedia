-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_LiftS_levi_isom
-- name    : GlobalTheory.DegCnt.LiftS.levi_isom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:42:53.982193+00:00
-- url     : https://prove2.me/theorems/0500b5d4-8484-4236-b25b-6d9b22ce175a
-- title:
--   Lift S: levi isom
-- statement:
--   The Lift S construction uses the levi isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L91-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L91-L173

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
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.DegCnt.LiftS.levi_isom (H : HermSpace K V) (p q : V →ₗ[K] V) (s : V ≃ₗ[K] V)
    (adj : ∀ x y, H.B (p x) y = H.B x (q y)) (pp : ∀ x, p (p x) = p x) (qq : ∀ x, q (q x) = q x)
    (pq : ∀ x, p (q x) = 0) (qp : ∀ x, q (p x) = 0) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)
    (h1 : ∀ x, p (s (p x)) = s (p x)) (h2 : ∀ x, p (s.symm (p x)) = s.symm (p x)) (x y : V) :
    H.B (levi p q s x) (levi p q s y) = H.B x y := by sorry
