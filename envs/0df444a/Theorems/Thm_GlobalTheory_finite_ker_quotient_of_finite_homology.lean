-- Prove2me | Theorems.Thm_GlobalTheory_finite_ker_quotient_of_finite_homology
-- name    : GlobalTheory.finite_ker_quotient_of_finite_homology
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:15.476635+00:00
-- url     : https://prove2.me/theorems/08bcf206-8cb2-41c3-bb18-faa1fc8cde88
-- title:
--   Global Theory: finite ker quotient of finite homology
-- statement:
--   The Global Theory construction uses the finite ker quotient of finite homology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L508-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L508-L519

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
open Limits
variable {R : Type u} [CommRing R]

theorem GlobalTheory.finite_ker_quotient_of_finite_homology (C : CochainComplex (ModuleCat.{v} R) ℕ)
    (i j k : ℕ) (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    [Module.Finite R (C.homology j)] :
    Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype) := by sorry
