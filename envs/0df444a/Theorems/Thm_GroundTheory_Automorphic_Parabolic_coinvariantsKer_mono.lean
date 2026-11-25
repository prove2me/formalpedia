-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_coinvariantsKer_mono
-- name    : GroundTheory.Automorphic.Parabolic.coinvariantsKer_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:25.379668+00:00
-- url     : https://prove2.me/theorems/a0a41d80-2334-5ac4-9261-bdfa6cef521b
-- title:
--   Parabolic: coinvariants Ker mono
-- statement:
--   The Parabolic construction uses the coinvariants Ker mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L38-L43

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}

theorem GroundTheory.Automorphic.Parabolic.coinvariantsKer_mono {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {H H' : Subgroup G} (h : H ≤ H') :
    coinvariantsKer ρ H ≤ coinvariantsKer ρ H' := by sorry
