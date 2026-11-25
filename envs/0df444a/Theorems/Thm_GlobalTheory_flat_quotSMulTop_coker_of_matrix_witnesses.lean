-- Prove2me | Theorems.Thm_GlobalTheory_flat_quotSMulTop_coker_of_matrix_witnesses
-- name    : GlobalTheory.flat_quotSMulTop_coker_of_matrix_witnesses
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:25.899437+00:00
-- url     : https://prove2.me/theorems/22f90822-c049-4b96-b236-fa77056b3328
-- title:
--   Global Theory: flat quot SMul Top coker of matrix witnesses
-- statement:
--   The Global Theory construction uses the flat quot SMul Top coker of matrix witnesses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FlatQuotSMulTopCokerOfMatrixWitnesses.lean#L10-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FlatQuotSMulTopCokerOfMatrixWitnesses.lean#L10-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FlatQuotSMulTopCokerOfMatrixWitnesses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise
open GlobalTheory

theorem GlobalTheory.flat_quotSMulTop_coker_of_matrix_witnesses :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (r a b : ℕ) (g : Fin r → S) (u : S) (Φ : Matrix (Fin a) (Fin b) S), Module.Flat R (S ⧸ Ideal.span (Set.range g)) → (∃ c : Fin r → S, u = ∑ k, c k * g k) → (∀ k, ∃ (C : Matrix (Fin b) (Fin a) S) (C' : Matrix (Fin a) (Fin a) S), g k • (1 : Matrix (Fin a) (Fin a) S) = Φ * C + u • C') → (∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S), Φ * Ψ * Φ = Φ + ∑ k, g k • E k) → Module.Flat R (QuotSMulTop u ((Fin a → S) ⧸ LinearMap.range Φ.mulVecLin)) := by sorry
