-- Prove2me | Theorems.Thm_GlobalTheory_GaloisLift_cong_pow_of_cong_pow_int
-- name    : GlobalTheory.GaloisLift.cong_pow_of_cong_pow_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:20:39.959127+00:00
-- url     : https://prove2.me/theorems/d92a42e7-b72c-4b6f-ac9b-d88495b0c8bf
-- title:
--   Galois Lift: cong pow of cong pow int
-- statement:
--   The Galois Lift construction uses the cong pow of cong pow int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFixingActsAsFrobeniusPowerResidue.lean#L8-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFixingActsAsFrobeniusPowerResidue.lean#L8-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixingActsAsFrobeniusPowerResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open Pointwise
open GlobalTheory GlobalTheory.GaloisLift

theorem GlobalTheory.GaloisLift.cong_pow_of_cong_pow_int (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) {σ : G E Ω} (hdec : σ ∈ Dec (F := E) A) {q : ℕ}
    (hcong : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b ^ q) < 1) :
    ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by sorry
