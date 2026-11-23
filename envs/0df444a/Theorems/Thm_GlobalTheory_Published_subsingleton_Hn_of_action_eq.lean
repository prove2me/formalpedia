-- Prove2me | Theorems.Thm_GlobalTheory_Published_subsingleton_Hn_of_action_eq
-- name    : GlobalTheory.Published.subsingleton_Hn_of_action_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:58.697789+00:00
-- url     : https://prove2.me/theorems/91f8f5a2-2ec1-43ac-9121-f75c253751f6
-- title:
--   Published: subsingleton Hn of action eq
-- statement:
--   The Published construction uses the subsingleton Hn of action eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/CohDimTwoLocalOfLocalFiniteness.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/CohDimTwoLocalOfLocalFiniteness.lean#L61-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.Published
variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {M : Type*} [AddCommGroup M]
  [TopologicalSpace M] [IsTopologicalAddGroup M]

theorem GlobalTheory.Published.subsingleton_Hn_of_action_eq {R R' : Type*} [CommRing R] [CommRing R'] [Module R M]
    [Module R' M] [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
    (rho : Representation R Γ M) (rho' : Representation R' Γ M)
    (h : ∀ g m, rho g m = rho' g m) (n : ℕ) (hn : 0 < n) (hs : Subsingleton (Hn rho' n)) :
    Subsingleton (Hn rho n) := by sorry
