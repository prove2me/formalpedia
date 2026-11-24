-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_gramR_ratTup
-- name    : GlobalTheory.CompanionTheory.SW.GramLocal.gramR_ratTup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:59.263994+00:00
-- url     : https://prove2.me/theorems/8705e7c3-f803-41a4-859e-37b038f322ec
-- title:
--   Gram Local: gram R rat Tup
-- statement:
--   The Gram Local construction uses the gram R rat Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L49-L53

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

theorem GlobalTheory.CompanionTheory.SW.GramLocal.gramR_ratTup (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) :
    gramR R σ J (ratTup R Y) = (gramE σ J Y).map (inclR R) := by sorry
