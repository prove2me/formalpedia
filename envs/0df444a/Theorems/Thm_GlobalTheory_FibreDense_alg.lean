-- Prove2me | Theorems.Thm_GlobalTheory_FibreDense_alg
-- name    : GlobalTheory.FibreDense.alg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:34:01.112821+00:00
-- url     : https://prove2.me/theorems/4ce78dc5-1e6f-5670-b320-3464fcaadbb2
-- title:
--   Fibre Dense: alg
-- statement:
--   The Fibre Dense construction uses the alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtOfAgreeOnFibreDenseOpenSmooth.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtOfAgreeOnFibreDenseOpenSmooth.lean#L11-L26

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

theorem GlobalTheory.FibreDense.alg (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b : B)
    (h : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q})) : b = 0 := by sorry
