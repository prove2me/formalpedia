-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_bcE_sigR
-- name    : GlobalTheory.CompanionTheory.SW.GramLocal.bcE_sigR
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:46.9837+00:00
-- url     : https://prove2.me/theorems/958fd6fa-300c-4b47-b14e-324a138918f2
-- title:
--   Gram Local: bc E sig R
-- statement:
--   The Gram Local construction uses the bc E sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L22-L27

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramLocal
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

theorem GlobalTheory.CompanionTheory.SW.GramLocal.bcE_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    bcE E f (sigR R σ z) = sigR S σ (bcE E f z) := by sorry
