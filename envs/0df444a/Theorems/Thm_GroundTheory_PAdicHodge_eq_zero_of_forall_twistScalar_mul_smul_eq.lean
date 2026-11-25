-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_eq_zero_of_forall_twistScalar_mul_smul_eq
-- name    : GroundTheory.PAdicHodge.eq_zero_of_forall_twistScalar_mul_smul_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:11:35.849796+00:00
-- url     : https://prove2.me/theorems/c1e46763-8bfd-4556-aecf-3c91ccc43d83
-- title:
--   PAdic Hodge: eq zero of forall twist Scalar mul smul eq
-- statement:
--   The PAdic Hodge construction uses the eq zero of forall twist Scalar mul smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L220-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L220-L282

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.PAdicHodge.eq_zero_of_forall_twistScalar_mul_smul_eq {j : ℤ} (hj : j ≠ 0) {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), twistScalar K j σ * (σ • x) = x) : x = 0 := by sorry
