-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CoordMat_traceGram_isSymm
-- name    : GlobalTheory.CompanionTheory.SW.CoordMat.traceGram_isSymm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:43.13935+00:00
-- url     : https://prove2.me/theorems/687f9b8b-a441-4c04-a55a-4eefeb373478
-- title:
--   Coord Mat: trace Gram is Symm
-- statement:
--   The Coord Mat construction uses the trace Gram is Symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L93-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L93-L104

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

theorem GlobalTheory.CompanionTheory.SW.CoordMat.traceGram_isSymm [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j) (b : Module.Basis (Fin d) F E) :
    (traceGram σ J b).IsSymm := by sorry
