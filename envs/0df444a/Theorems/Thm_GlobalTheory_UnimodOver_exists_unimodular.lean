-- Prove2me | Theorems.Thm_GlobalTheory_UnimodOver_exists_unimodular
-- name    : GlobalTheory.UnimodOver.exists_unimodular
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:27.189207+00:00
-- url     : https://prove2.me/theorems/3fa10575-e287-46f7-ba16-450a2e71a1db
-- title:
--   Unimod Over: exists unimodular
-- statement:
--   The Unimod Over construction uses the exists unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L126-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L126-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem GlobalTheory.UnimodOver.exists_unimodular (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ (M : Submodule ℤ V) (N : ℕ) (Ef : LinearMap.BilinForm ℤ M),
      Λ ≤ M ∧ 0 < N ∧ (∀ x ∈ M, N • x ∈ Λ) ∧ DiscreteTopology M ∧
      Submodule.span ℝ (M : Set V) = ⊤ ∧ (∀ a b : M, (Ef a b : ℝ) = B a b) ∧
      Function.Bijective Ef := by sorry
