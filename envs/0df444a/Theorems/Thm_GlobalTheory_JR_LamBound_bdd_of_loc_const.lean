-- Prove2me | Theorems.Thm_GlobalTheory_JR_LamBound_bdd_of_loc_const
-- name    : GlobalTheory.JR.LamBound.bdd_of_loc_const
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:33:39.391285+00:00
-- url     : https://prove2.me/theorems/974a4917-bac0-4966-a33c-1960d306bf4d
-- title:
--   Lam Bound: bdd of loc const
-- statement:
--   The Lam Bound construction uses the bdd of loc const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerBoundBigCell.lean#L21-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerBoundBigCell.lean#L21-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerBoundBigCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LamBound
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.LamBound.bdd_of_loc_const (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (O : Set K) (hO : IsCompact O) (Ψ : SpecialLinearGroup (Fin 2) K → ℂ) (U : Set K) (hU : U ∈ 𝓝 (0 : K))
    (hΨ : ∀ g k : SpecialLinearGroup (Fin 2) K, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) K) - 1) i j ∈ U) →
      Ψ (g * k) = Ψ g) :
    ∃ C : ℝ, ∀ k : SpecialLinearGroup (Fin 2) K, (∀ i j, (k : Matrix (Fin 2) (Fin 2) K) i j ∈ O) → ‖Ψ k‖ ≤ C := by sorry
