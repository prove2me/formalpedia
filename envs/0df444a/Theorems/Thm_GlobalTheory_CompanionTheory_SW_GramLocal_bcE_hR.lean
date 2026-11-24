-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_bcE_hR
-- name    : GlobalTheory.CompanionTheory.SW.GramLocal.bcE_hR
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:50.709499+00:00
-- url     : https://prove2.me/theorems/a5571051-3184-4eaa-a812-02bde3e4cacb
-- title:
--   Gram Local: bc E h R
-- statement:
--   The Gram Local construction uses the bc E h R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L29-L32

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

theorem GlobalTheory.CompanionTheory.SW.GramLocal.bcE_hR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y : Fin M → R ⊗[F] E) :
    bcE E f (hR R σ J x y) = hR S σ J (fun i => bcE E f (x i)) (fun i => bcE E f (y i)) := by sorry
