-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_heckeAct_comp
-- name    : GroundTheory.Automorphic.ContragredientTranspose.heckeAct_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:57:43.698846+00:00
-- url     : https://prove2.me/theorems/e769439f-3767-45e8-9535-50026251021f
-- title:
--   Contragredient Transpose: hecke Act comp
-- statement:
--   The Contragredient Transpose construction uses the hecke Act comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L267-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L267-L284

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MeasureTheory Module Whittaker
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Automorphic.ContragredientTranspose.heckeAct_comp (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm)
    (hμ : μ.map α = μ) (f : locallyConstantCompactSupport G ℂ ℂ) {v : V}
    (hv : v ∈ smoothVectors ρ) (hv' : v ∈ smoothVectors (ρ.comp α.toMonoidHom)) :
    heckeAct μ (ρ.comp α.toMonoidHom) (f : G → ℂ) v =
      heckeAct μ ρ ((compHomeoL (mulEquivHomeo α hα hα').symm f :
        locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) v := by sorry
