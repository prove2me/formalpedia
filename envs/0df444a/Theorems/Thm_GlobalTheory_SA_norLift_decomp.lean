-- Prove2me | Theorems.Thm_GlobalTheory_SA_norLift_decomp
-- name    : GlobalTheory.SA.norLift_decomp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:46:15.876406+00:00
-- url     : https://prove2.me/theorems/aee726c7-2a49-4b66-900e-1a4564721b14
-- title:
--   SA: nor Lift decomp
-- statement:
--   The SA construction uses the nor Lift decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinrankLeFinrankInfPerpXPlus.lean#L25-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinrankLeFinrankInfPerpXPlus.lean#L25-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinrankLeFinrankInfPerpXPlus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA
open GlobalTheory GlobalTheory.SA

theorem GlobalTheory.SA.norLift_decomp : ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r), IsTransv F F' →
    Module.finrank K (norLift F F') = r + 1 ∧ norLift F F' ⊔ norLift F' F = V0 F F' ∧
    wSp F F' ⊔ norLift F F' = perp H (xPlus F) ∧ Disjoint (wSp F F') (norLift F F') ∧
    IsCompl (V0 F F') (wSp F F') := by sorry
