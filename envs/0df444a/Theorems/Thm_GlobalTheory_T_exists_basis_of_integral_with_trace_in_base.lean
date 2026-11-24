-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_basis_of_integral_with_trace_in_base
-- name    : GlobalTheory.T.exists_basis_of_integral_with_trace_in_base
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:33:32.448956+00:00
-- url     : https://prove2.me/theorems/8095bd56-e427-4b06-a185-1647da78ba29
-- title:
--   T: exists basis of integral with trace in base
-- statement:
--   The T construction uses the exists basis of integral with trace in base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsBasisInFiniteDomainTraceMemStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsBasisInFiniteDomainTraceMemStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBasisInFiniteDomainTraceMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBasisInFiniteDomainTraceMemStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_basis_of_integral_with_trace_in_base : ∀ (T C F K : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CommRing C] [IsDomain C] [Field F] [Field K] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C], ∃ (n : ℕ) (b : Module.Basis (Fin n) F K), (∀ i, ∃ c : C, algebraMap C K c = b i) ∧ ∀ i j, ∃ t : T, algebraMap T F t = Algebra.trace F K (b i * b j) := by sorry
