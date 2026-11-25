-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_injective_of_isBaseChange_of_flat
-- name    : GlobalTheory.QCoh.injective_of_isBaseChange_of_flat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:02:55.338719+00:00
-- url     : https://prove2.me/theorems/1e50db2d-d82d-4305-aa6a-4ba38c9c5e57
-- title:
--   QCoh: injective of is Base Change of flat
-- statement:
--   The QCoh construction uses the injective of is Base Change of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L585-L597
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L585-L597

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}} {F F' : X.Modules}
variable (f : X ⟶ Y)

theorem GlobalTheory.QCoh.injective_of_isBaseChange_of_flat {A B M M' N N' : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [AddCommGroup N']
    [Module A N'] [Module B N'] [IsScalarTower A B N'] {l : M →ₗ[A] N} {l' : M' →ₗ[A] N'}
    (hl : IsBaseChange B l) (hl' : IsBaseChange B l') (a : M →ₗ[A] M') (b : N →ₗ[B] N')
    (hab : ∀ m, b (l m) = l' (a m)) (ha : Function.Injective a) : Function.Injective b := by sorry
