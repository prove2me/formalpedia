-- Prove2me | Theorems.Thm_GlobalTheory_BaseChangeComponents_range_comp_incl
-- name    : GlobalTheory.BaseChangeComponents.range_comp_incl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:36.632207+00:00
-- url     : https://prove2.me/theorems/7b186845-4aa4-49b9-b818-c55ccfc0f3a8
-- title:
--   Base Change Components: range comp incl
-- statement:
--   The Base Change Components construction uses the range comp incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L87-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L87-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]

theorem GlobalTheory.BaseChangeComponents.range_comp_incl {E : Type} [CommRing E] (R : Subalgebra K Ω) (g : F ⊗[K] Ω →+* E) :
    (g.comp (incl F R)).range = Subring.closure
      ((g.comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω)
        ∪ Set.range (g.comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) := by sorry
