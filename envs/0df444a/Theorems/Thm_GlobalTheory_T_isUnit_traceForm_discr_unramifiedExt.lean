-- Prove2me | Theorems.Thm_GlobalTheory_T_isUnit_traceForm_discr_unramifiedExt
-- name    : GlobalTheory.T.isUnit_traceForm_discr_unramifiedExt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:24.04764+00:00
-- url     : https://prove2.me/theorems/28303778-6a84-4516-ab23-decce5fff9d0
-- title:
--   T: is Unit trace Form discr unramified Ext
-- statement:
--   The T construction uses the is Unit trace Form discr unramified Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitTraceFormDiscrUnramifiedExtStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitTraceFormDiscrUnramifiedExtStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitTraceFormDiscrUnramifiedExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitTraceFormDiscrUnramifiedExtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isUnit_traceForm_discr_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (π : K.O) (π' : K'.O), algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) → IsLocalRing.maximalIdeal K.O = Ideal.span {π} → IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det := by sorry
