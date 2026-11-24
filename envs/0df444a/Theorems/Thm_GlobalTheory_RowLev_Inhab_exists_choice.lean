-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_Inhab_exists_choice
-- name    : GlobalTheory.RowLev.Inhab.exists_choice
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:30:48.302993+00:00
-- url     : https://prove2.me/theorems/c1cc812a-dbb0-4af0-aed6-e20de0663ce4
-- title:
--   Inhab: exists choice
-- statement:
--   The Inhab construction uses the exists choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L489-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L489-L558

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.Inhab

theorem GlobalTheory.RowLev.Inhab.exists_choice (I : AutInst) (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      Ideal.absNorm v.asIdeal = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ v.asIdeal ^ 2 ∧ ¬ IsConj I v v) :
    ∃ (Pl : Fin 2 → Type) (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)), (∀ k, Nonempty (Pl k)) ∧
      IsChoice I g Pl w := by sorry
