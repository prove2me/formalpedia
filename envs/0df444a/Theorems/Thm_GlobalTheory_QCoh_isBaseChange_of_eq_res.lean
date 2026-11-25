-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isBaseChange_of_eq_res
-- name    : GlobalTheory.QCoh.isBaseChange_of_eq_res
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:34.095091+00:00
-- url     : https://prove2.me/theorems/fc2b4335-ed47-4a18-8738-d7b18840830a
-- title:
--   QCoh: is Base Change of eq res
-- statement:
--   The QCoh construction uses the is Base Change of eq res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L398-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L398-L409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}

theorem GlobalTheory.QCoh.isBaseChange_of_eq_res [F.IsQuasicoherent] (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) [alg : Algebra Γ(X, U) Γ(X, V)] [mod : Module Γ(X, U) Γ(F, V)]
    [IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V)]
    (halg : ∀ r, algebraMap Γ(X, U) Γ(X, V) r = X.presheaf.map (homOfLE h).op r)
    (l : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V)) (hl : ∀ s, l s = F.presheaf.map (homOfLE h).op s) :
    IsBaseChange Γ(X, V) l := by sorry
