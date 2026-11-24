-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CoordMat_trace_expand
-- name    : GlobalTheory.CompanionTheory.SW.CoordMat.trace_expand
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:18.49173+00:00
-- url     : https://prove2.me/theorems/503df756-d652-454b-841a-9db781f835ea
-- title:
--   Coord Mat: trace expand
-- statement:
--   The Coord Mat construction uses the trace expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L32-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L32-L58

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceGramDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CoordMat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.CoordMat.trace_expand [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * inclR R e * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by sorry
