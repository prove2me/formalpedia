-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedEmbedding_range_le_range_of_isUnramifiedAt
-- name    : GlobalTheory.UnramifiedEmbedding.range_le_range_of_isUnramifiedAt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:24.481299+00:00
-- url     : https://prove2.me/theorems/2e2918ba-9f07-55e9-9829-f0236dc9b1b3
-- title:
--   Unramified Embedding: range le range of is Unramified At
-- statement:
--   The Unramified Embedding construction uses the range le range of is Unramified At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RangeLeRangeOfIsUnramifiedAt.lean#L56-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RangeLeRangeOfIsUnramifiedAt.lean#L56-L199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RangeLeRangeOfIsUnramifiedAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing NumberField
open GlobalTheory GlobalTheory.UnramifiedEmbedding

theorem GlobalTheory.UnramifiedEmbedding.range_le_range_of_isUnramifiedAt
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [IsAlgClosed (ResidueField O)]
    (l : ℕ) [Fact l.Prime] (hl : (l : O) ∈ maximalIdeal O)
    (e : FractionRing O →+* ℂ)
    (K₀ L : Type) [Field K₀] [NumberField K₀] [Field L] [NumberField L] [Algebra K₀ L]
    (ι : K₀ →+* FractionRing O) (σ : L →+* ℂ) (hσ : σ.comp (algebraMap K₀ L) = e.comp ι)
    (hur : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], (l : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 K₀) P) :
    σ.range ≤ e.range := by sorry
