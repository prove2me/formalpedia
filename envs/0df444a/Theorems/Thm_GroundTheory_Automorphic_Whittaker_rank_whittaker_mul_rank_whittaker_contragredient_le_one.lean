-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_rank_whittaker_mul_rank_whittaker_contragredient_le_one
-- name    : GroundTheory.Automorphic.Whittaker.rank_whittaker_mul_rank_whittaker_contragredient_le_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:57.269283+00:00
-- url     : https://prove2.me/theorems/448602a8-4822-4d64-9428-fd3f234cc5c3
-- title:
--   Whittaker: rank whittaker mul rank whittaker contragredient le one
-- statement:
--   The Whittaker construction uses the rank whittaker mul rank whittaker contragredient le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLocal.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLocal.lean#L78-L89

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open MeasureTheory Measure ValuativeRel
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.Whittaker.rank_whittaker_mul_rank_whittaker_contragredient_le_one (ψ₀ : AddChar F ℂ)
    (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Module.rank ℂ (equivariantFunctionals π
        (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) *
      Module.rank ℂ (equivariantFunctionals (contragredient π)
        (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹)) ≤ 1 := by sorry
