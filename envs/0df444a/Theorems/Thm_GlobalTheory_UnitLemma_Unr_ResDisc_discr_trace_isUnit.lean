-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResDisc_discr_trace_isUnit
-- name    : GlobalTheory.UnitLemma.Unr.ResDisc.discr_trace_isUnit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:35:50.969281+00:00
-- url     : https://prove2.me/theorems/e42518d0-c01f-436e-a6ea-c4773f7cd902
-- title:
--   Res Disc: discr trace is Unit
-- statement:
--   The Res Disc construction uses the discr trace is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitTraceFormDiscrUnramifiedExt.lean#L37-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitTraceFormDiscrUnramifiedExt.lean#L37-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitTraceFormDiscrUnramifiedExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResDisc
open IsLocalRing

theorem GlobalTheory.UnitLemma.Unr.ResDisc.discr_trace_isUnit : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (π : K.O) (π' : K'.O), algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) → IsLocalRing.maximalIdeal K.O = Ideal.span {π} → IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det := by sorry
