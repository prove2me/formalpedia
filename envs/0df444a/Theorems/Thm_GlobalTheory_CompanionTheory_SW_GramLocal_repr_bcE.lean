-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_repr_bcE
-- name    : GlobalTheory.CompanionTheory.SW.GramLocal.repr_bcE
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:46.493452+00:00
-- url     : https://prove2.me/theorems/f5adb4a7-992f-4c3d-87fa-10dac7c2b2b6
-- title:
--   Gram Local: repr bc E
-- statement:
--   The Gram Local construction uses the repr bc E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L40-L47

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

theorem GlobalTheory.CompanionTheory.SW.GramLocal.repr_bcE {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) (f : R →ₐ[F] S)
    (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr (bcE E f z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by sorry
