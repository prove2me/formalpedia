-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_iterate_frobeniusEquiv_symm_mem_integerTilt
-- name    : GroundTheory.PAdicHodge.iterate_frobeniusEquiv_symm_mem_integerTilt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:39.927898+00:00
-- url     : https://prove2.me/theorems/7566cf67-ed6c-4070-ae0a-38a75d8129d9
-- title:
--   PAdic Hodge: iterate frobenius Equiv symm mem integer Tilt
-- statement:
--   The PAdic Hodge construction uses the iterate frobenius Equiv symm mem integer Tilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltPerfectoid.lean#L182-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltPerfectoid.lean#L182-L189

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltDegree
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem GroundTheory.PAdicHodge.iterate_frobeniusEquiv_symm_mem_integerTilt {N : IntermediateField K♭ C♭}
    [FiniteDimensional K♭ N] {a : 𝒪C♭} (ha : a ∈ integerTilt K C p N) (n : ℕ) :
    (frobeniusEquiv 𝒪C♭ p).symm^[n] a ∈ integerTilt K C p N := by sorry
