-- Prove2me | Theorems.Thm_GlobalTheory_BaseChangeComponents_incl_injective
-- name    : GlobalTheory.BaseChangeComponents.incl_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:32.828348+00:00
-- url     : https://prove2.me/theorems/b955b755-3bdb-492a-a0ef-02adcc70317e
-- title:
--   Base Change Components: incl injective
-- statement:
--   The Base Change Components construction uses the incl injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L16-L20

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

theorem GlobalTheory.BaseChangeComponents.incl_injective (R : Subalgebra K Ω) : Function.Injective (incl F R) := by sorry
