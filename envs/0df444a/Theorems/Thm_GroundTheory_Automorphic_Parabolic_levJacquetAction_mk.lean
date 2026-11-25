-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_levJacquetAction_mk
-- name    : GroundTheory.Automorphic.Parabolic.levJacquetAction_mk
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:12:56.890099+00:00
-- url     : https://prove2.me/theorems/ffe71238-fab5-5ea8-be59-923e8c12fb8c
-- title:
--   Parabolic: lev Jacquet Action mk
-- statement:
--   The Parabolic construction uses the lev Jacquet Action mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L246-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L246-L249

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCharacters
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
  {n : ℕ}
variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

theorem GroundTheory.Automorphic.Parabolic.levJacquetAction_mk {δ : Fin n → ℕ}
    (x : (levi F n β ⊓ blockUpper F n δ : Subgroup (GL (Fin n) F))) (v : W) :
    levJacquetAction β σ δ x (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (σ (leviInfIncl β δ x) v) := by sorry
