-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_mem_range_algebraMap_of_forall_algEquiv
-- name    : GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:21.582801+00:00
-- url     : https://prove2.me/theorems/37305f47-0dfd-4af6-87ed-7f3fd809ca1b
-- title:
--   Galois Descent: mem range algebra Map of forall alg Equiv
-- statement:
--   The Galois Descent construction uses the mem range algebra Map of forall alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsRingEquivOfIsTranscendenceBasis.lean#L69-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsRingEquivOfIsTranscendenceBasis.lean#L69-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Cardinal
open GlobalTheory GlobalTheory.GaloisDescent
open MvPolynomial Cardinal

theorem GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    [PerfectField K] [IsAlgClosed L] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    x ∈ Set.range (algebraMap K L) := by sorry
