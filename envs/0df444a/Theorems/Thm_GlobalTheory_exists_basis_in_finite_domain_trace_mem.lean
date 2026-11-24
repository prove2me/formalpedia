-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_in_finite_domain_trace_mem
-- name    : GlobalTheory.exists_basis_in_finite_domain_trace_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:27.921532+00:00
-- url     : https://prove2.me/theorems/9d12a934-7eb6-4331-896a-e7e1eee876ea
-- title:
--   Global Theory: exists basis in finite domain trace mem
-- statement:
--   The Global Theory construction uses the exists basis in finite domain trace mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsBasisInFiniteDomainTraceMem.lean#L6-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsBasisInFiniteDomainTraceMem.lean#L6-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBasisInFiniteDomainTraceMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_basis_in_finite_domain_trace_mem (T C F K : Type) [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] [CommRing C] [IsDomain C] [Field F] [Field K] [Algebra T C]
    [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra T K]
    [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F K),
      (∀ (i : Fin n), ∃ (c : C), (algebraMap C K : C → K) c = (b : Fin n → K) i) ∧
        ∀ (i j : Fin n), ∃ (t : T), (algebraMap T F : T → F) t =
          (Algebra.trace F K : K → F) ((b : Fin n → K) i * (b : Fin n → K) j) := by sorry
