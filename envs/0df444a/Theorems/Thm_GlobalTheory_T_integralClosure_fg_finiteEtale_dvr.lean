-- Prove2me | Theorems.Thm_GlobalTheory_T_integralClosure_fg_finiteEtale_dvr
-- name    : GlobalTheory.T.integralClosure_fg_finiteEtale_dvr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:34:16.572476+00:00
-- url     : https://prove2.me/theorems/dac4bedc-431c-489f-856a-a47e2f73272f
-- title:
--   T: integral Closure fg finite Etale dvr
-- statement:
--   The T construction uses the integral Closure fg finite Etale dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgFiniteEtaleDvrStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgFiniteEtaleDvrStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgFiniteEtaleDvr
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgFiniteEtaleDvrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integralClosure_fg_finiteEtale_dvr : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A], (Subalgebra.toSubmodule (integralClosure O A)).FG := by sorry
