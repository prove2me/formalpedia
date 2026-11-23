-- Prove2me | Theorems.Thm_GroundTheory_LocalField_CharZero_finiteDimensional_padicHom
-- name    : GroundTheory.LocalField.CharZero.finiteDimensional_padicHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:15.872192+00:00
-- url     : https://prove2.me/theorems/2771dbdc-9df7-43e3-8ba1-d5fc58bbe616
-- title:
--   Char Zero: finite Dimensional padic Hom
-- statement:
--   The Char Zero construction uses the finite Dimensional padic Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L175-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L175-L185

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel WithZero Topology
open GroundTheory.LocalField.CharZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [CharP 𝓀[K] p]
variable [Fact p.Prime]
variable [CharZero K]

theorem GroundTheory.LocalField.CharZero.finiteDimensional_padicHom :
    letI := (padicHom K p).toAlgebra
    FiniteDimensional ℚ_[p] K := by sorry
