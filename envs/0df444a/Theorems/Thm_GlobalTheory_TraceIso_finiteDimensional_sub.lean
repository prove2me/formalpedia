-- Prove2me | Theorems.Thm_GlobalTheory_TraceIso_finiteDimensional_sub
-- name    : GlobalTheory.TraceIso.finiteDimensional_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:37.034714+00:00
-- url     : https://prove2.me/theorems/2d933a6d-4396-4ad2-ae4b-5eb6d1957172
-- title:
--   Trace Iso: finite Dimensional sub
-- statement:
--   The Trace Iso construction uses the finite Dimensional sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyLinearEquivOfCharpolyEq.lean#L35-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyLinearEquivOfCharpolyEq.lean#L35-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceIso
open Module
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

theorem GlobalTheory.TraceIso.finiteDimensional_sub [FiniteDimensional k V] (P : Submodule A V) : FiniteDimensional k P := by sorry
