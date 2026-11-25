-- Prove2me | Theorems.Thm_GlobalTheory_FibreDense_dense
-- name    : GlobalTheory.FibreDense.dense
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:23:59.995026+00:00
-- url     : https://prove2.me/theorems/76dc2839-d0b6-473b-9857-1781a1bcf065
-- title:
--   Fibre Dense: dense
-- statement:
--   The Fibre Dense construction uses the dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtOfAgreeOnFibreDenseOpenSmooth.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtOfAgreeOnFibreDenseOpenSmooth.lean#L28-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchemeTheoreticallyDominantOfGermInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreDenseAffineChartPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnnihilatorAvoidsFibreMinimalPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinimStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonZeroDivisorLocalizationGeneralOfNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtOfAgreeOnFibreDenseOpenSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibreDense

theorem GlobalTheory.FibreDense.dense (X T : Scheme.{0}) (p : X ⟶ T) [Smooth p] (W : X.Opens)
    (hW : ∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) : IsSchemeTheoreticallyDominant W.ι := by sorry
