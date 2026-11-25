-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_FrameMove_coeff_mem
-- name    : GlobalTheory.DegAsm.FrameMove.coeff_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:24:03.721046+00:00
-- url     : https://prove2.me/theorems/1278d902-4a97-41b8-b59d-17f77b9aea9a
-- title:
--   Frame Move: coeff mem
-- statement:
--   The Frame Move construction uses the coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SmulMemOfOne.lean#L207-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SmulMemOfOne.lean#L207-L236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
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
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.FrameMove
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegAsm.FrameMove.coeff_mem (G : FlagD H r) {Λ : Submodule (𝓞 K) V} {aa : Fin r → Submodule (𝓞 K) K}
    (h1 : ∀ (a : Fin r) (t : K), ∀ x ∈ Λ, x - t • G.e a.castSucc ∈ G.Xa a.val → t ∈ aa a)
    (h2 : ∀ a, ∀ t ∈ aa a, t • G.e a.castSucc ∈ Λ) (n : ℕ) :
    ∀ c : Fin r → K, (∀ b : Fin r, n ≤ b.val → c b = 0) → ∑ b, c b • G.e b.castSucc ∈ Λ → ∀ b, c b ∈ aa b := by sorry
