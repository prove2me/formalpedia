-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isIrreducible_contragredient
-- name    : GroundTheory.Automorphic.Whittaker.isIrreducible_contragredient
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:02:10.66631+00:00
-- url     : https://prove2.me/theorems/3712e6f2-7fee-44d3-b3e8-fa1868ef48fb
-- title:
--   Whittaker: is Irreducible contragredient
-- statement:
--   The Whittaker construction uses the is Irreducible contragredient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L464-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L464-L487

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
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
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.Whittaker.isIrreducible_contragredient (h : IsAdmissible ρ) [ρ.IsIrreducible] :
    (contragredient ρ).IsIrreducible := by sorry
