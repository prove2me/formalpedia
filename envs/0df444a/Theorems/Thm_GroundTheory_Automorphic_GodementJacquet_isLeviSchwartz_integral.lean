-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_isLeviSchwartz_integral
-- name    : GroundTheory.Automorphic.GodementJacquet.isLeviSchwartz_integral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:37.846428+00:00
-- url     : https://prove2.me/theorems/d0f36460-b377-416b-b130-7097ebe56594
-- title:
--   Godement Jacquet: is Levi Schwartz integral
-- statement:
--   The Godement Jacquet construction uses the is Levi Schwartz integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L560-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L560-L583

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJParabolicFubini
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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable {β : Fin n → α}

theorem GroundTheory.Automorphic.GodementJacquet.isLeviSchwartz_integral (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔫.IsAddHaarMeasure]
    {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    IsLeviSchwartz β (fun X => ∫ u, Φ (X + unipMatrix F u) ∂μ𝔫) := by sorry
