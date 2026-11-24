-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IwasawaOf_spherical_mem
-- name    : GlobalTheory.Doubling.IwasawaOf.spherical_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:08.054449+00:00
-- url     : https://prove2.me/theorems/5037efa5-ffec-4c3c-bbc7-aefb6ef15929
-- title:
--   Iwasawa Of: spherical mem
-- statement:
--   The Iwasawa Of construction uses the spherical mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L507-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L507-L510

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
open scoped NNReal
open MeasureTheory
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A) (ν : Aˣ →* ℝ≥0) (K : Subgroup G)
variable {e mat ν K}
variable [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.Doubling.IwasawaOf.spherical_mem (h : IwasawaOf e mat ν K) (hm : Continuous mat) (hν : Continuous ν)
    (hK : IsCompact (K : Set G)) (s : ℂ) :
    (fun g => npow (hgtOf e mat ν K g) (s + (Fintype.card n : ℂ) / 2)) ∈ degPSOf e mat ν K 1 s := by sorry
