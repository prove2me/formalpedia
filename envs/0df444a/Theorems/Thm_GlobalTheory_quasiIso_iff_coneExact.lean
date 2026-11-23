-- Prove2me | Theorems.Thm_GlobalTheory_quasiIso_iff_coneExact
-- name    : GlobalTheory.quasiIso_iff_coneExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:03.808918+00:00
-- url     : https://prove2.me/theorems/655ad948-c8dd-4434-b808-7ed1b5633dfe
-- title:
--   Global Theory: quasi Iso iff cone Exact
-- statement:
--   The Global Theory construction uses the quasi Iso iff cone Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L430-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L430-L461

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
variable {R : Type u} [Ring R]

theorem GlobalTheory.quasiIso_iff_coneExact {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) :
    QuasiIso φ ↔ ConeExact (K := fun p => K.X p) (C := fun p => C.X p)
      (fun p => (K.d p (p + 1)).hom) (fun p => (C.d p (p + 1)).hom) (fun p => (φ.f p).hom) := by sorry
