-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_NFUnique_main
-- name    : GlobalTheory.DegAsm.NFUnique.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:11:19.071495+00:00
-- url     : https://prove2.me/theorems/1ba04edf-bf11-4f40-a0cf-94d65ede9c44
-- title:
--   NFUnique: main
-- statement:
--   The NFUnique construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L121-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L121-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable [NumberField K]
variable [FiniteDimensional K V]

theorem GlobalTheory.DegAsm.NFUnique.main (N₀ N₁ : NF H r) (h : SameGr N₀.F N₁.F) (hj : N₀.j = N₁.j) (hc : N₀.c = N₁.c) (hT : N₀.T = N₁.T)
    (hM : pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j) :
    ∃ s : V ≃ₗ[K] V, N₀.F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by sorry
