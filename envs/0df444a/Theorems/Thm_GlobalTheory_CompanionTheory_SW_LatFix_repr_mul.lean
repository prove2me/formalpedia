-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatFix_repr_mul
-- name    : GlobalTheory.CompanionTheory.SW.LatFix.repr_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:06:36.143506+00:00
-- url     : https://prove2.me/theorems/299806b7-7474-40a3-ae05-5ec0592d1a92
-- title:
--   Lat Fix: repr mul
-- statement:
--   The Lat Fix construction uses the repr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EventuallyActMemLatVIff.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EventuallyActMemLatVIff.lean#L16-L29

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyActMemLatVIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatFix
variable {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.LatFix.repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (x y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (x * y) k =
      ∑ i, ∑ j, (Algebra.TensorProduct.basis R b).repr x i *
        (Algebra.TensorProduct.basis R b).repr y j * algebraMap F R (b.repr (b i * b j) k) := by sorry
