-- Prove2me | Theorems.Thm_GlobalTheory_IntegralClosureFG_integralClosure_fg
-- name    : GlobalTheory.IntegralClosureFG.integralClosure_fg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:19:40.88059+00:00
-- url     : https://prove2.me/theorems/26f84803-e8af-4184-9042-d0d8cbcbe82f
-- title:
--   Integral Closure FG: integral Closure fg
-- statement:
--   The Integral Closure FG construction uses the integral Closure fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgFiniteEtaleDvr.lean#L7-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgFiniteEtaleDvr.lean#L7-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgFiniteEtaleDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralClosureFG

theorem GlobalTheory.IntegralClosureFG.integralClosure_fg (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A] :
    (Subalgebra.toSubmodule (integralClosure O A)).FG := by sorry
