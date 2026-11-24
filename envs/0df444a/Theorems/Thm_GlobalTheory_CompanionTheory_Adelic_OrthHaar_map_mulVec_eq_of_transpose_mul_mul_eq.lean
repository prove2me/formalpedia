-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_OrthHaar_map_mulVec_eq_of_transpose_mul_mul_eq
-- name    : GlobalTheory.CompanionTheory.Adelic.OrthHaar.map_mulVec_eq_of_transpose_mul_mul_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:16:31.72903+00:00
-- url     : https://prove2.me/theorems/37d9fb32-d262-4975-a45b-a63e1812b6e6
-- title:
--   Orth Haar: map mul Vec eq of transpose mul mul eq
-- statement:
--   The Orth Haar construction uses the map mul Vec eq of transpose mul mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqOfTransposeMulMulEq.lean#L126-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqOfTransposeMulMulEq.lean#L126-L155

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqOfTransposeMulMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.OrthHaar

theorem GlobalTheory.CompanionTheory.Adelic.OrthHaar.map_mulVec_eq_of_transpose_mul_mul_eq :
    ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
      [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R],
      (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → R)) [μ.IsAddHaarMeasure]
        (B g : Matrix ι ι R), IsUnit B.det → gᵀ * B * g = B →
        μ.map (fun x => g *ᵥ x) = μ := by sorry
