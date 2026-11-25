-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_glEquiv_eq_one
-- name    : GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv_eq_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:14:50.016785+00:00
-- url     : https://prove2.me/theorems/e72af955-7164-439e-b5b4-965786e4ec15
-- title:
--   Measures: distrib Haar Char gl Equiv eq one
-- statement:
--   The Measures construction uses the distrib Haar Char gl Equiv eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L162-L169

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} {ι : Type*} [Fintype ι]
variable [DecidableEq ι]

theorem GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv_eq_one {g : GL ι F} (h₁ : ∀ a b, (g : Matrix ι ι F) a b ∈ 𝒪[F])
    (h₂ : ∀ a b, ((g⁻¹ : GL ι F) : Matrix ι ι F) a b ∈ 𝒪[F]) :
    distribHaarChar (ι → F) (glEquiv g) = 1 := by sorry
