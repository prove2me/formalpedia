-- Prove2me | Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
-- name    : GlobalTheory.LengthQuotientSpanValuation.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:31.199567+00:00
-- url     : https://prove2.me/theorems/1f566724-d7b5-4db0-b687-01e0e2b4d991
-- title:
--   Length Quotient Span Valuation: main
-- statement:
--   The Length Quotient Span Valuation construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthSelfEqTop.lean#L31-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthSelfEqTop.lean#L31-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthSelfEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.LengthQuotientSpanValuation
open Module

theorem GlobalTheory.LengthQuotientSpanValuation.main {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {M : Type u_2} [AddCommGroup M] [Module R M] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {M' : Type u_4} [AddCommGroup M'] [Module R M'] (b' : Module.Basis ι R M')
    (b : Module.Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      (IsDiscreteValuationRing.addVal R : R → ℕ∞)
        (Matrix.det ((LinearMap.toMatrix b' b : (M' →ₗ[R] M) → Matrix ι ι R) f)) := by sorry
