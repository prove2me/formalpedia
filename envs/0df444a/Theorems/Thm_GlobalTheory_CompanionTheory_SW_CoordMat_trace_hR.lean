-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CoordMat_trace_hR
-- name    : GlobalTheory.CompanionTheory.SW.CoordMat.trace_hR
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:09.726004+00:00
-- url     : https://prove2.me/theorems/74e0aee8-4618-448a-b44e-0c4c1c2cb772
-- title:
--   Coord Mat: trace h R
-- statement:
--   The Coord Mat construction uses the trace h R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L60-L68

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

theorem GlobalTheory.CompanionTheory.SW.CoordMat.trace_hR [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (x y : Fin M → R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      coordL R M b x ⬝ᵥ (traceGram σ J b).map (algebraMap F R) *ᵥ coordL R M b y := by sorry
