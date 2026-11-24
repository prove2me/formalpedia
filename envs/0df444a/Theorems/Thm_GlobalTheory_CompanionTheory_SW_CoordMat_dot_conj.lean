-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CoordMat_dot_conj
-- name    : GlobalTheory.CompanionTheory.SW.CoordMat.dot_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:40.252723+00:00
-- url     : https://prove2.me/theorems/edad1743-5b8a-4594-b72b-03a71284cf27
-- title:
--   Coord Mat: dot conj
-- statement:
--   The Coord Mat construction uses the dot conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean#L88-L91

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

theorem GlobalTheory.CompanionTheory.SW.CoordMat.dot_conj {ι A : Type} [Fintype ι] [CommRing A] (g P : Matrix ι ι A) (u v : ι → A) :
    u ⬝ᵥ (gᵀ * P * g) *ᵥ v = (g *ᵥ u) ⬝ᵥ P *ᵥ (g *ᵥ v) := by sorry
