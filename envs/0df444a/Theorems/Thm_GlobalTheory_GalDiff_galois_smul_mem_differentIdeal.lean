-- Prove2me | Theorems.Thm_GlobalTheory_GalDiff_galois_smul_mem_differentIdeal
-- name    : GlobalTheory.GalDiff.galois_smul_mem_differentIdeal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:37.184597+00:00
-- url     : https://prove2.me/theorems/0936a143-5a7d-456e-9b0d-588f7637389f
-- title:
--   Gal Diff: galois smul mem different Ideal
-- statement:
--   The Gal Diff construction uses the galois smul mem different Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentIdealPowFinrankEqSpanDiscr.lean#L26-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentIdealPowFinrankEqSpanDiscr.lean#L26-L45

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

theorem GlobalTheory.GalDiff.galois_smul_mem_differentIdeal (σ : E ≃ₐ[ℚ] E) {x : 𝓞 E}
    (hx : x ∈ differentIdeal ℤ (𝓞 E)) : σ • x ∈ differentIdeal ℤ (𝓞 E) := by sorry
