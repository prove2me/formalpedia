-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFamily_exists_quotient_closure
-- name    : GlobalTheory.ThetaFamily.exists_quotient_closure
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:54.643834+00:00
-- url     : https://prove2.me/theorems/e9d52a2d-7c09-401b-8bc0-94a7f48482ae
-- title:
--   Theta Family: exists quotient closure
-- statement:
--   The Theta Family construction uses the exists quotient closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfFiniteOfClosedFibres.lean#L11-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfFiniteOfClosedFibres.lean#L11-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaFamily

theorem GlobalTheory.ThetaFamily.exists_quotient_closure {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] {W : Set (V × V')}
    {f θ : V × V' → ℂ} (hW : IsOpen W) (hf : DifferentiableOn ℂ f W) (hθ : DifferentiableOn ℂ θ W) {S : Set V}
    (hS : ∀ b ∈ S, ∃ F : V' → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W} ∧ ∀ z, (b, z) ∈ W → F z * θ (b, z) = f (b, z))
    {w : V × V'} (hw : w ∈ W) (hfr : ∃ᶠ z in 𝓝 w.2, θ (w.1, z) ≠ 0) :
    ∃ (U : Set (V × V')) (G : V × V' → ℂ), IsOpen U ∧ w ∈ U ∧ U ⊆ W ∧ DifferentiableOn ℂ G U ∧
      ∀ y ∈ U, y.1 ∈ closure S → G y * θ y = f y := by sorry
