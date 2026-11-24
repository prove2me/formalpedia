-- Prove2me | Theorems.Thm_GlobalTheory_GalDiff_differentIdeal_pow_finrank_eq_span_discr
-- name    : GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:39.288039+00:00
-- url     : https://prove2.me/theorems/cc4bf594-739b-43df-b4d0-b5d59e5216a7
-- title:
--   Gal Diff: different Ideal pow finrank eq span discr
-- statement:
--   The Gal Diff construction uses the different Ideal pow finrank eq span discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentIdealPowFinrankEqSpanDiscr.lean#L47-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentIdealPowFinrankEqSpanDiscr.lean#L47-L82

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentIdealPowFinrankEqSpanDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.GalDiff
open scoped Pointwise
variable (E : Type) [Field E] [NumberField E]

theorem GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr :
    ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F],
      differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by sorry
