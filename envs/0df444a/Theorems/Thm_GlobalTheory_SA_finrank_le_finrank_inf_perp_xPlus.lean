-- Prove2me | Theorems.Thm_GlobalTheory_SA_finrank_le_finrank_inf_perp_xPlus
-- name    : GlobalTheory.SA.finrank_le_finrank_inf_perp_xPlus
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:48:56.309344+00:00
-- url     : https://prove2.me/theorems/fe92025e-7727-49ed-a134-6c0e4461f4b0
-- title:
--   SA: finrank le finrank inf perp x Plus
-- statement:
--   The SA construction uses the finrank le finrank inf perp x Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinrankLeFinrankInfPerpXPlus.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinrankLeFinrankInfPerpXPlus.lean#L7-L23

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

theorem GlobalTheory.SA.finrank_le_finrank_inf_perp_xPlus {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ} (S : Submodule K V) (F : FlagD H r) :
    Module.finrank K S ≤ Module.finrank K ↥(S ⊓ perp H (xPlus F)) + (r + 1) := by sorry
