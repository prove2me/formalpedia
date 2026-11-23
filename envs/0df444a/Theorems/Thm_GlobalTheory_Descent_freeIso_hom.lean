-- Prove2me | Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- name    : GlobalTheory.Descent.freeIso_hom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:55.85134+00:00
-- url     : https://prove2.me/theorems/5e694ebc-99d8-4497-bf32-e8a671f2468b
-- title:
--   Descent: free Iso hom
-- statement:
--   The Descent construction uses the free Iso hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L243-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L243-L246

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.Descent
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (F : X.Modules)
variable {F} {U : X.Opens} {s : Γ(F, U)}

theorem GlobalTheory.Descent.freeIso_hom
    (h : ∀ (x : X) (hx : x ∈ U), Function.Bijective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s) :
    (freeIso h).hom = sectionHom s := by sorry

attribute [defeq] GlobalTheory.Descent.freeIso_hom
