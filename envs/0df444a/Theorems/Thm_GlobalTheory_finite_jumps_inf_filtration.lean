-- Prove2me | Theorems.Thm_GlobalTheory_finite_jumps_inf_filtration
-- name    : GlobalTheory.finite_jumps_inf_filtration
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:32.098261+00:00
-- url     : https://prove2.me/theorems/14f3a9ae-9218-4876-a944-a9eabb4c4f2e
-- title:
--   Global Theory: finite jumps inf filtration
-- statement:
--   The Global Theory construction uses the finite jumps inf filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteJumpsInfFiltration.lean#L5-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteJumpsInfFiltration.lean#L5-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteJumpsInfFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finite_jumps_inf_filtration (E W : Type) [Field E] [AddCommGroup W] [Module E W]
    (D : Submodule E W) (F : ℤ → Submodule E W) (hD : Module.Finite E ↥D)
    (hF : ∀ a, F (a + 1) ≤ F a) :
    {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by sorry
