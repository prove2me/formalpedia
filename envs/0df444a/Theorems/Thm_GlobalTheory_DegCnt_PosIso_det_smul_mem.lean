-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosIso_det_smul_mem
-- name    : GlobalTheory.DegCnt.PosIso.det_smul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:25:00.906501+00:00
-- url     : https://prove2.me/theorems/94b2f6f2-886b-4ec8-a6ed-0398c281efec
-- title:
--   Pos Iso: det smul mem
-- statement:
--   The Pos Iso construction uses the det smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L52-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L52-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K]

theorem GlobalTheory.DegCnt.PosIso.det_smul_mem (H : HermSpace K V) (Λ : Submodule (𝓞 K) V) {j : ℕ} (x x' : Fin j → V)
    (hx : ∀ a, x a ∈ Λ) (hG : ∀ a b, H.B (x a) (x' b) ∈ (1 : Submodule (𝓞 K) K)) (p : Fin j → K)
    (hp : ∀ b, H.B (∑ a, p a • x a) (x' b) ∈ (1 : Submodule (𝓞 K) K)) :
    (Matrix.of fun a b => H.B (x a) (x' b)).det • (∑ a, p a • x a) ∈ Λ := by sorry
