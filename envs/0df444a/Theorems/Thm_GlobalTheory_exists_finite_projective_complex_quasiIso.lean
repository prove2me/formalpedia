-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_projective_complex_quasiIso
-- name    : GlobalTheory.exists_finite_projective_complex_quasiIso
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:38.529065+00:00
-- url     : https://prove2.me/theorems/42032707-3296-4582-949b-3fe042d59eb1
-- title:
--   Global Theory: exists finite projective complex quasi Iso
-- statement:
--   The Global Theory construction uses the exists finite projective complex quasi Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L597-L620
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L597-L620

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

theorem GlobalTheory.exists_finite_projective_complex_quasiIso [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hflat : ∀ p, Module.Flat R (C.X p)) (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℕ) (φ : K ⟶ C),
      (∀ p, n < p → IsZero (K.X p)) ∧ (∀ p, Module.Finite R (K.X p)) ∧
      (∀ p, 1 ≤ p → Module.Free R (K.X p)) ∧ (∀ p, Module.Projective R (K.X p)) ∧
      QuasiIso φ ∧
      (∀ M : ModuleCat.{u} R,
        QuasiIso (((MonoidalCategory.tensorLeft M).mapHomologicalComplex _).map φ)) ∧
      (∀ (S : Type w) [CommRing S] [Algebra R S], QuasiIso
        (((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex _).map φ)) := by sorry
