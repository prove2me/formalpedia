-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_parabolicIndSpace
-- name    : GroundTheory.Automorphic.Parabolic.mem_parabolicIndSpace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:25.384552+00:00
-- url     : https://prove2.me/theorems/7bcf5d8e-6f89-4465-a275-c7bce3d06562
-- title:
--   Parabolic: mem parabolic Ind Space
-- statement:
--   The Parabolic construction uses the mem parabolic Ind Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolic.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolic.lean#L99-L104

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem GroundTheory.Automorphic.Parabolic.mem_parabolicIndSpace (σ : Representation ℂ (levi F n β) W) {f : GL (Fin n) F → W} :
    f ∈ parabolicIndSpace F n β σ ↔
      (∀ p : blockUpper F n β, ∀ g, f (p * g) = sqrtModular F n β p • σ (leviProj F n β p) (f g)) ∧
        ∃ K : Subgroup (GL (Fin n) F), IsOpen (K : Set (GL (Fin n) F)) ∧
          ∀ k ∈ K, ∀ g, f (g * k) = f g := by sorry
